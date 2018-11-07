extern crate sled_sync;

use std::cell::RefCell;
use std::sync::atomic::{AtomicUsize, Ordering::SeqCst};

use sled_sync::Atomic;

enum Error {
    Abort,
    Predicate,
}

enum State {
    Pending,
    Committed,
    Aborted,
    Unused,
}

struct RecordNode<T> {
    rts: AtomicUsize,
    wts: usize,
    state: State,
    data: T,
    next: Atomic<RecordNode<T>>,
}

#[derive(Clone)]
struct Record<T: Clone> {
    head: Atomic<RecordNode<T>>,
}

type ReadSet<T> = Vec<Record<T>>;
type WriteSet<T> = Vec<(Record<T>, T)>;

struct TxState<T: Clone> {
    read_set: ReadSet<T>,
    write_set: WriteSet<T>,
}

trait Tickable {
    type Success;

    fn tick(self) -> Result<Self::Success, Error>;
}

struct Begin<T: Clone>(TxState<T>);

impl<T: Clone> Tickable for Begin<T> {
    type Success = AllocateTimestamp<T>;

    fn tick(self) -> Result<Self::Success, Error> {
        Ok(AllocateTimestamp(self.0))
    }
}

struct AllocateTimestamp<T: Clone>(TxState<T>);

impl<T: Clone> Tickable for AllocateTimestamp<T> {
    type Success = SearchVersions<T>;

    fn tick(self) -> Result<Self::Success, Error> {
        Ok(SearchVersions(self.0))
    }
}

struct SearchVersions<T: Clone>(TxState<T>);

impl<T: Clone> Tickable for SearchVersions<T> {
    type Success = SortWriteSetByContention<T>;
    fn tick(self) -> Result<Self::Success, Error> {
        Ok(SortWriteSetByContention(self.0))
    }
}

struct SortWriteSetByContention<T: Clone>(TxState<T>);

impl<T: Clone> Tickable for SortWriteSetByContention<T> {
    type Success = PreCheckVersionConsistency<T>;
    fn tick(self) -> Result<Self::Success, Error> {
        Ok(PreCheckVersionConsistency(self.0))
    }
}

struct PreCheckVersionConsistency<T: Clone>(TxState<T>);

impl<T: Clone> Tickable for PreCheckVersionConsistency<T> {
    type Success = InstallPendingVersions<T>;
    fn tick(self) -> Result<Self::Success, Error> {
        Ok(InstallPendingVersions(self.0))
    }
}

struct InstallPendingVersions<T: Clone>(TxState<T>);

impl<T: Clone> Tickable for InstallPendingVersions<T> {
    type Success = UpdateReadTimestamp<T>;
    fn tick(self) -> Result<Self::Success, Error> {
        Ok(UpdateReadTimestamp(self.0))
    }
}

struct UpdateReadTimestamp<T: Clone>(TxState<T>);

impl<T: Clone> Tickable for UpdateReadTimestamp<T> {
    type Success = CheckVersionConsistency<T>;
    fn tick(self) -> Result<Self::Success, Error> {
        Ok(CheckVersionConsistency(self.0))
    }
}

struct CheckVersionConsistency<T: Clone>(TxState<T>);

impl<T: Clone> Tickable for CheckVersionConsistency<T> {
    type Success = LogWriteSet<T>;
    fn tick(self) -> Result<Self::Success, Error> {
        Ok(LogWriteSet(self.0))
    }
}

struct LogWriteSet<T: Clone>(TxState<T>);

impl<T: Clone> Tickable for LogWriteSet<T> {
    type Success = CommitPendingVersions<T>;
    fn tick(self) -> Result<Self::Success, Error> {
        Ok(CommitPendingVersions(self.0))
    }
}

struct CommitPendingVersions<T: Clone>(TxState<T>);

impl<T: Clone> Tickable for CommitPendingVersions<T> {
    type Success = ScheduleGarbageCollection<T>;
    fn tick(self) -> Result<Self::Success, Error> {
        Ok(ScheduleGarbageCollection(self.0))
    }
}

struct ScheduleGarbageCollection<T: Clone>(TxState<T>);

impl<T: Clone> Tickable for ScheduleGarbageCollection<T> {
    type Success = Committed<T>;
    fn tick(self) -> Result<Self::Success, Error> {
        Ok(Committed(self.0))
    }
}

struct DeclareQuiescentState<T: Clone>(TxState<T>);

struct Committed<T: Clone>(TxState<T>);

fn bump_rts(txid: usize, au: &AtomicUsize) {
    let mut cur = au.load(SeqCst);
    while cur < txid {
        let res = au.compare_and_swap(cur, txid, SeqCst);
        if res == cur {
            return;
        }
        cur = res;
    }
}

fn execute<T: Clone>(
    reads: ReadSet<T>,
    writes: WriteSet<T>,
    max_retries: usize,
) -> Result<Committed<T>, Error> {
    let tx_state = TxState {
        read_set: reads.clone(),
        write_set: writes.clone(),
    };

    match try_exec(tx_state) {
        Err(Error::Abort) => {
            if max_retries == 0 {
                Err(Error::Abort)
            } else {
                backoff();
                execute(reads, writes, max_retries - 1)
            }
        }
        success_or_predicate_error => success_or_predicate_error,
    }
}

fn try_exec<T: Clone>(
    tx_state: TxState<T>,
) -> Result<Committed<T>, Error> {
    let begin = Begin(tx_state);
    let allocate_ts = begin.tick()?;
    let search_versions = allocate_ts.tick()?;
    let sort_write_set_by_contention = search_versions.tick()?;
    let pre_check_version_consistency =
        sort_write_set_by_contention.tick()?;
    let install_pending_versions =
        pre_check_version_consistency.tick()?;
    let update_read_timestamp = install_pending_versions.tick()?;
    let check_version_consistency = update_read_timestamp.tick()?;
    let log_write_set = check_version_consistency.tick()?;
    let commit_pending_versions = log_write_set.tick()?;
    let schedule_garbage_collection =
        commit_pending_versions.tick()?;
    let committed = schedule_garbage_collection.tick()?;

    Ok(committed)
}

fn backoff() {}

thread_local! {
    static ATTEMPTS: RefCell<(usize, [bool; 5])> = RefCell::new((0, [false;5]));
}
