//! # Working with `Log`
//!
//! ```
//! let config = pagecache::ConfigBuilder::new()
//!     .temporary(true)
//!     .segment_mode(pagecache::SegmentMode::Linear)
//!     .build();
//! let log = pagecache::Log::start_raw_log(config).unwrap();
//! let (first_lsn, _first_offset) = log.write(b"1".to_vec()).unwrap();
//! log.write(b"22".to_vec()).unwrap();
//! log.write(b"333".to_vec()).unwrap();
//!
//! // stick an abort in the middle, which should not be returned
//! let res = log.reserve(b"never_gonna_hit_disk".to_vec()).unwrap();
//! res.abort().unwrap();
//!
//! log.write(b"4444".to_vec());
//! let (last_lsn, _last_offset) = log.write(b"55555".to_vec()).unwrap();
//! log.make_stable(last_lsn).unwrap();
//! let mut iter = log.iter_from(first_lsn);
//! assert_eq!(iter.next().unwrap().2, b"1".to_vec());
//! assert_eq!(iter.next().unwrap().2, b"22".to_vec());
//! assert_eq!(iter.next().unwrap().2, b"333".to_vec());
//! assert_eq!(iter.next().unwrap().2, b"4444".to_vec());
//! assert_eq!(iter.next().unwrap().2, b"55555".to_vec());
//! assert_eq!(iter.next(), None);
//! ```
use std::sync::Arc;

use super::*;

/// A sequential store which allows users to create
/// reservations placed at known log offsets, used
/// for writing persistent data structures that need
/// to know where to find persisted bits in the future.
pub struct Log {
    /// iobufs is the underlying lock-free IO write buffer.
    pub(super) iobufs: Arc<IoBufs>,
    config: Config,
    /// Periodically flushes `iobufs`.
    _flusher: Option<flusher::Flusher>,
}

unsafe impl Send for Log {}

impl Log {
    /// Start the log, open or create the configured file,
    /// and optionally start the periodic buffer flush thread.
    pub fn start<R>(
        config: Config,
        snapshot: Snapshot<R>,
    ) -> Result<Log, ()> {
        let iobufs =
            Arc::new(IoBufs::start(config.clone(), snapshot)?);
        let flusher = config.flush_every_ms.map(|fem| {
            flusher::Flusher::new(
                "log flusher".to_owned(),
                iobufs.clone(),
                fem,
            )
        });

        Ok(Log {
            iobufs,
            config,
            _flusher: flusher,
        })
    }

    /// Starts a log for use without a materializer.
    pub fn start_raw_log(config: Config) -> Result<Log, ()> {
        assert_eq!(config.segment_mode, SegmentMode::Linear);
        let log_iter = raw_segment_iter_from(0, &config)?;

        let snapshot = advance_snapshot::<NullMaterializer, (), ()>(
            log_iter,
            Snapshot::default(),
            &config,
        )?;

        Log::start::<()>(config, snapshot)
    }

    /// Flushes any pending IO buffers to disk to ensure durability.
    pub fn flush(&self) -> Result<(), ()> {
        self.iobufs.flush()
    }

    /// Reserve space in the log for a pending linearized operation.
    pub fn reserve(
        &self,
        buf: Vec<u8>,
    ) -> Result<Reservation<'_>, ()> {
        self.iobufs.reserve(buf)
    }

    /// Reserve a replacement buffer for a previously written
    /// blob write. This ensures the message header has the
    /// proper blob flag set.
    pub(super) fn reserve_blob(
        &self,
        blob_ptr: BlobPointer,
    ) -> Result<Reservation<'_>, ()> {
        self.iobufs.reserve_blob(blob_ptr)
    }

    /// Write a buffer into the log. Returns the log sequence
    /// number and the file offset of the write.
    pub fn write(&self, buf: Vec<u8>) -> Result<(Lsn, DiskPtr), ()> {
        self.iobufs.reserve(buf).and_then(|res| res.complete())
    }

    /// Return an iterator over the log, starting with
    /// a specified offset.
    pub fn iter_from(&self, lsn: Lsn) -> LogIter {
        self.iobufs.iter_from(lsn)
    }

    /// read a buffer from the disk
    pub fn read(
        &self,
        lsn: Lsn,
        ptr: DiskPtr,
    ) -> Result<LogRead, ()> {
        trace!("reading log lsn {} ptr {}", lsn, ptr);

        self.make_stable(lsn)?;

        if ptr.is_inline() {
            let lid = ptr.inline();
            let f = self.config.file()?;

            let read = f.read_message(lid, &self.config);

            read.and_then(|log_read| match log_read {
                LogRead::Inline(read_lsn, _, _)
                | LogRead::Blob(read_lsn, _, _) => {
                    if lsn != read_lsn {
                        Err(Error::Corruption { at: ptr })
                    } else {
                        Ok(log_read)
                    }
                }
                _ => Ok(log_read),
            })
            .map_err(|e| e)
        } else {
            let (_lid, blob_ptr) = ptr.blob();
            read_blob(blob_ptr, &self.config)
                .map(|buf| LogRead::Blob(lsn, buf, blob_ptr))
        }
    }

    /// returns the current stable offset written to disk
    pub fn stable_offset(&self) -> Lsn {
        self.iobufs.stable()
    }

    /// blocks until the specified log sequence number has
    /// been made stable on disk
    pub fn make_stable(&self, lsn: Lsn) -> Result<(), ()> {
        self.iobufs.make_stable(lsn)
    }

    // SegmentAccountant access for coordination with the `PageCache`
    pub(crate) fn with_sa<B, F>(&self, f: F) -> B
    where
        F: FnOnce(&mut SegmentAccountant) -> B,
    {
        self.iobufs.with_sa(f)
    }
}

/// Represents the kind of message written to the log
#[derive(Debug, Copy, Clone, PartialEq)]
pub(crate) enum MessageKind {
    Inline,
    Blob,
    Failed,
    Pad,
    Corrupted,
}

/// All log messages are prepended with this header
#[derive(Debug, Copy, Clone, PartialEq)]
pub(crate) struct MessageHeader {
    pub(crate) kind: MessageKind,
    pub(crate) lsn: Lsn,
    pub(crate) len: usize,
    pub(crate) crc16: [u8; 2],
}

/// A segment's header contains the new base LSN and a reference
/// to the previous log segment.
#[derive(Debug, Copy, Clone, PartialEq)]
pub(crate) struct SegmentHeader {
    pub(crate) lsn: Lsn,
    pub(crate) ok: bool,
}

/// A segment's trailer contains the base Lsn for the segment.
/// It is written after the rest of the segment has been fsync'd,
/// and helps us indicate if a segment has been torn.
#[derive(Debug, Copy, Clone, PartialEq)]
pub(crate) struct SegmentTrailer {
    pub(crate) lsn: Lsn,
    pub(crate) ok: bool,
}

#[doc(hidden)]
#[derive(Debug)]
pub enum LogRead {
    Inline(Lsn, Vec<u8>, usize),
    Blob(Lsn, Vec<u8>, BlobPointer),
    Failed(Lsn, usize),
    Pad(Lsn),
    Corrupted(usize),
    DanglingBlob(Lsn, BlobPointer),
}

impl LogRead {
    /// Optionally return successfully read inline bytes, or
    /// None if the data was corrupt or this log entry was aborted.
    pub fn inline(self) -> Option<(Lsn, Vec<u8>, usize)> {
        match self {
            LogRead::Inline(lsn, bytes, len) => {
                Some((lsn, bytes, len))
            }
            _ => None,
        }
    }

    /// Return true if this is an Inline value..
    pub fn is_inline(&self) -> bool {
        match *self {
            LogRead::Inline(_, _, _) => true,
            _ => false,
        }
    }

    /// Optionally return a successfully read pointer to an
    /// blob value, or None if the data was corrupt or
    /// this log entry was aborted.
    pub fn blob(self) -> Option<(Lsn, Vec<u8>, BlobPointer)> {
        match self {
            LogRead::Blob(lsn, buf, ptr) => Some((lsn, buf, ptr)),
            _ => None,
        }
    }

    /// Return true if we read a completed blob write successfully.
    pub fn is_blob(&self) -> bool {
        match self {
            LogRead::Blob(..) => true,
            _ => false,
        }
    }

    /// Return true if we read an aborted flush.
    pub fn is_failed(&self) -> bool {
        match *self {
            LogRead::Failed(_, _) => true,
            _ => false,
        }
    }

    /// Return true if we read a successful Inline or Blob value.
    pub fn is_successful(&self) -> bool {
        match *self {
            LogRead::Inline(_, _, _) | LogRead::Blob(_, _, _) => true,
            _ => false,
        }
    }

    /// Return true if we read a segment pad.
    pub fn is_pad(&self) -> bool {
        match *self {
            LogRead::Pad(_) => true,
            _ => false,
        }
    }

    /// Return true if we read a corrupted log entry.
    pub fn is_corrupt(&self) -> bool {
        match *self {
            LogRead::Corrupted(_) => true,
            _ => false,
        }
    }

    /// Return the underlying data read from a log read, if successful.
    pub fn into_data(self) -> Option<Vec<u8>> {
        match self {
            LogRead::Blob(_, buf, _) | LogRead::Inline(_, buf, _) => {
                Some(buf)
            }
            _ => None,
        }
    }
}

// NB we use a lot of xors below to differentiate between zeroed out
// data on disk and an lsn or crc16 of 0

impl From<[u8; MSG_HEADER_LEN]> for MessageHeader {
    fn from(buf: [u8; MSG_HEADER_LEN]) -> MessageHeader {
        let kind = match buf[0] {
            INLINE_FLUSH => MessageKind::Inline,
            BLOB_FLUSH => MessageKind::Blob,
            FAILED_FLUSH => MessageKind::Failed,
            SEGMENT_PAD => MessageKind::Pad,
            _ => MessageKind::Corrupted,
        };

        let lsn_buf = &buf[1..9];
        let mut lsn_arr = [0u8; 8];
        lsn_arr.copy_from_slice(&*lsn_buf);
        let lsn = arr_to_u64(lsn_arr) as Lsn;

        let len_buf = &buf[9..13];
        let mut len_arr = [0u8; 4];
        len_arr.copy_from_slice(&*len_buf);
        let len = arr_to_u32(len_arr);

        let crc16 = [buf[13] ^ 0xFF, buf[14] ^ 0xFF];

        MessageHeader {
            kind,
            lsn,
            len: len as usize,
            crc16,
        }
    }
}

impl Into<[u8; MSG_HEADER_LEN]> for MessageHeader {
    fn into(self) -> [u8; MSG_HEADER_LEN] {
        let mut buf = [0u8; MSG_HEADER_LEN];
        buf[0] = match self.kind {
            MessageKind::Inline => INLINE_FLUSH,
            MessageKind::Blob => BLOB_FLUSH,
            MessageKind::Failed => FAILED_FLUSH,
            MessageKind::Pad => SEGMENT_PAD,
            MessageKind::Corrupted => EVIL_BYTE,
        };

        // NB LSN actually gets written after the reservation
        // for the item is claimed, when we actually know the lsn,
        // in PageCache::reserve.
        let lsn_arr = u64_to_arr(self.lsn as u64);
        buf[1..9].copy_from_slice(&lsn_arr);

        assert!(self.len <= std::u32::MAX as usize);
        let len_arr = u32_to_arr(self.len as u32);
        buf[9..13].copy_from_slice(&len_arr);

        buf[13] = self.crc16[0] ^ 0xFF;
        buf[14] = self.crc16[1] ^ 0xFF;

        buf
    }
}

impl From<[u8; SEG_HEADER_LEN]> for SegmentHeader {
    fn from(buf: [u8; SEG_HEADER_LEN]) -> SegmentHeader {
        let crc16 = [buf[0] ^ 0xFF, buf[1] ^ 0xFF];

        let lsn_buf = &buf[2..10];
        let mut lsn_arr = [0u8; 8];
        lsn_arr.copy_from_slice(&*lsn_buf);
        let xor_lsn = arr_to_u64(lsn_arr) as Lsn;
        let lsn = xor_lsn ^ 0xFFFF_FFFF;

        let crc16_tested = crc16_arr(&lsn_arr);

        SegmentHeader {
            lsn,
            ok: crc16_tested == crc16,
        }
    }
}

impl Into<[u8; SEG_HEADER_LEN]> for SegmentHeader {
    fn into(self) -> [u8; SEG_HEADER_LEN] {
        let mut buf = [0u8; SEG_HEADER_LEN];

        let xor_lsn = self.lsn ^ 0xFFFF_FFFF;
        let lsn_arr = u64_to_arr(xor_lsn as u64);
        buf[2..10].copy_from_slice(&lsn_arr);

        let crc16 = crc16_arr(&lsn_arr);

        buf[0] = crc16[0] ^ 0xFF;
        buf[1] = crc16[1] ^ 0xFF;

        buf
    }
}

impl From<[u8; SEG_TRAILER_LEN]> for SegmentTrailer {
    fn from(buf: [u8; SEG_TRAILER_LEN]) -> SegmentTrailer {
        let crc16 = [buf[0] ^ 0xFF, buf[1] ^ 0xFF];

        let lsn_buf = &buf[2..10];
        let mut lsn_arr = [0u8; 8];
        lsn_arr.copy_from_slice(&*lsn_buf);
        let xor_lsn = arr_to_u64(lsn_arr) as Lsn;
        let lsn = xor_lsn ^ 0xFFFF_FFFF;

        let crc16_tested = crc16_arr(&lsn_arr);

        SegmentTrailer {
            lsn,
            ok: crc16_tested == crc16,
        }
    }
}

impl Into<[u8; SEG_TRAILER_LEN]> for SegmentTrailer {
    fn into(self) -> [u8; SEG_TRAILER_LEN] {
        let mut buf = [0u8; SEG_TRAILER_LEN];

        let xor_lsn = self.lsn ^ 0xFFFF_FFFF;
        let lsn_arr = u64_to_arr(xor_lsn as u64);
        buf[2..10].copy_from_slice(&lsn_arr);

        let crc16 = crc16_arr(&lsn_arr);
        buf[0] = crc16[0] ^ 0xFF;
        buf[1] = crc16[1] ^ 0xFF;

        buf
    }
}
