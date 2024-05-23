------------------------------ MODULE rwmutex ------------------------------
EXTENDS Integers, Naturals, TLC, Sequences, FiniteSets

CONSTANTS
Procs,
MaxReaders

ASSUME Cardinality(Procs) <= MaxReaders


(*--algorithm rwmutex {
variables 
    readers = 0; \* number of readers
    intentToWrite = FALSE;
    writeLockTaken = FALSE;
define {

HasPendingWriterOrTooManyReaders == intentToWrite \/ readers > MaxReaders

\* Invariants
TypeOK ==   /\ intentToWrite \in BOOLEAN
            /\ writeLockTaken \in BOOLEAN
            /\ readers \in Nat

OnlyOneWriterInCriticalSection ==
    \A a, b \in Procs : pc[a] = "wl_critical_section" =>
                            \/a = b
                            \/ pc[b] /= "wl_critical_section"

NoReadersAndWritersInCriticalSection ==
    \A a, b \in Procs : /\ pc[a] = "wl_critical_section" => pc[b] /= "rl_critical_section"

BaitOnlyOneReaderInCriticalSection ==
    \A a, b \in Procs : pc[a] = "rl_critical_section" =>
                            \/ a = b
                            \/ pc[b] /= "rl_critical_section"

\* Temporal properties
WritersEventuallyTakeLock ==
    \A p \in Procs: pc[p] = "wl_set_intent" ~> pc[p]= "wl_critical_section"

BaitReadersEventuallyTakeLock ==
    \A p \in Procs: pc[p] = "rl_add_and_fetch" ~> pc[p]= "rl_critical_section"

}

fair process (p \in Procs) 
variables
    localReaderCount = 0;
    localWriteIntent = FALSE;
{
process_start:
while(TRUE) {
    either {
wl_take_mutex:
        await (writeLockTaken = FALSE);
        writeLockTaken := TRUE;
wl_set_intent:
        assert (intentToWrite = FALSE);
        intentToWrite := TRUE;
wl_drain_readers:
        await (readers = 0);
wl_critical_section:
        skip;
wl_remove_intent:
        intentToWrite := FALSE;
wl_release_mutex:
        writeLockTaken := FALSE
    } or {
rl_add_and_fetch:
        readers := readers + 1;
        localReaderCount := readers;
rl_check_slow_path:
        while (HasPendingWriterOrTooManyReaders) {
            assert readers <= MaxReaders;
rl_unlock_shared:
            readers := readers - 1;
rl_drain_writers:
            await (intentToWrite = FALSE);
rl_add_and_fetch2:
            readers := readers + 1;
        };
rl_critical_section:
        skip;
rl_unlock_shared2:
        readers := readers - 1;
    }
    
}
}



} *)
\* BEGIN TRANSLATION (chksum(pcal) = "da51a193" /\ chksum(tla) = "34c94b5a")
VARIABLES readers, intentToWrite, writeLockTaken, pc

(* define statement *)
HasPendingWriterOrTooManyReaders == intentToWrite \/ readers > MaxReaders


TypeOK ==   /\ intentToWrite \in BOOLEAN
            /\ writeLockTaken \in BOOLEAN
            /\ readers \in Nat

OnlyOneWriterInCriticalSection ==
    \A a, b \in Procs : pc[a] = "wl_critical_section" =>
                            \/a = b
                            \/ pc[b] /= "wl_critical_section"

NoReadersAndWritersInCriticalSection ==
    \A a, b \in Procs : /\ pc[a] = "wl_critical_section" => pc[b] /= "rl_critical_section"

BaitOnlyOneReaderInCriticalSection ==
    \A a, b \in Procs : pc[a] = "rl_critical_section" =>
                            \/ a = b
                            \/ pc[b] /= "rl_critical_section"


WritersEventuallyTakeLock ==
    \A p \in Procs: pc[p] = "wl_set_intent" ~> pc[p]= "wl_critical_section"

BaitReadersEventuallyTakeLock ==
    \A p \in Procs: pc[p] = "rl_add_and_fetch" ~> pc[p]= "rl_critical_section"

VARIABLES localReaderCount, localWriteIntent

vars == << readers, intentToWrite, writeLockTaken, pc, localReaderCount, 
           localWriteIntent >>

ProcSet == (Procs)

Init == (* Global variables *)
        /\ readers = 0
        /\ intentToWrite = FALSE
        /\ writeLockTaken = FALSE
        (* Process p *)
        /\ localReaderCount = [self \in Procs |-> 0]
        /\ localWriteIntent = [self \in Procs |-> FALSE]
        /\ pc = [self \in ProcSet |-> "process_start"]

process_start(self) == /\ pc[self] = "process_start"
                       /\ \/ /\ pc' = [pc EXCEPT ![self] = "wl_take_mutex"]
                          \/ /\ pc' = [pc EXCEPT ![self] = "rl_add_and_fetch"]
                       /\ UNCHANGED << readers, intentToWrite, writeLockTaken, 
                                       localReaderCount, localWriteIntent >>

wl_take_mutex(self) == /\ pc[self] = "wl_take_mutex"
                       /\ (writeLockTaken = FALSE)
                       /\ writeLockTaken' = TRUE
                       /\ pc' = [pc EXCEPT ![self] = "wl_set_intent"]
                       /\ UNCHANGED << readers, intentToWrite, 
                                       localReaderCount, localWriteIntent >>

wl_set_intent(self) == /\ pc[self] = "wl_set_intent"
                       /\ Assert((intentToWrite = FALSE), 
                                 "Failure of assertion at line 59, column 9.")
                       /\ intentToWrite' = TRUE
                       /\ pc' = [pc EXCEPT ![self] = "wl_drain_readers"]
                       /\ UNCHANGED << readers, writeLockTaken, 
                                       localReaderCount, localWriteIntent >>

wl_drain_readers(self) == /\ pc[self] = "wl_drain_readers"
                          /\ (readers = 0)
                          /\ pc' = [pc EXCEPT ![self] = "wl_critical_section"]
                          /\ UNCHANGED << readers, intentToWrite, 
                                          writeLockTaken, localReaderCount, 
                                          localWriteIntent >>

wl_critical_section(self) == /\ pc[self] = "wl_critical_section"
                             /\ TRUE
                             /\ pc' = [pc EXCEPT ![self] = "wl_remove_intent"]
                             /\ UNCHANGED << readers, intentToWrite, 
                                             writeLockTaken, localReaderCount, 
                                             localWriteIntent >>

wl_remove_intent(self) == /\ pc[self] = "wl_remove_intent"
                          /\ intentToWrite' = FALSE
                          /\ pc' = [pc EXCEPT ![self] = "wl_release_mutex"]
                          /\ UNCHANGED << readers, writeLockTaken, 
                                          localReaderCount, localWriteIntent >>

wl_release_mutex(self) == /\ pc[self] = "wl_release_mutex"
                          /\ writeLockTaken' = FALSE
                          /\ pc' = [pc EXCEPT ![self] = "process_start"]
                          /\ UNCHANGED << readers, intentToWrite, 
                                          localReaderCount, localWriteIntent >>

rl_add_and_fetch(self) == /\ pc[self] = "rl_add_and_fetch"
                          /\ readers' = readers + 1
                          /\ localReaderCount' = [localReaderCount EXCEPT ![self] = readers']
                          /\ pc' = [pc EXCEPT ![self] = "rl_check_slow_path"]
                          /\ UNCHANGED << intentToWrite, writeLockTaken, 
                                          localWriteIntent >>

rl_check_slow_path(self) == /\ pc[self] = "rl_check_slow_path"
                            /\ IF HasPendingWriterOrTooManyReaders
                                  THEN /\ Assert(readers <= MaxReaders, 
                                                 "Failure of assertion at line 75, column 13.")
                                       /\ pc' = [pc EXCEPT ![self] = "rl_unlock_shared"]
                                  ELSE /\ pc' = [pc EXCEPT ![self] = "rl_critical_section"]
                            /\ UNCHANGED << readers, intentToWrite, 
                                            writeLockTaken, localReaderCount, 
                                            localWriteIntent >>

rl_unlock_shared(self) == /\ pc[self] = "rl_unlock_shared"
                          /\ readers' = readers - 1
                          /\ pc' = [pc EXCEPT ![self] = "rl_drain_writers"]
                          /\ UNCHANGED << intentToWrite, writeLockTaken, 
                                          localReaderCount, localWriteIntent >>

rl_drain_writers(self) == /\ pc[self] = "rl_drain_writers"
                          /\ (intentToWrite = FALSE)
                          /\ pc' = [pc EXCEPT ![self] = "rl_add_and_fetch2"]
                          /\ UNCHANGED << readers, intentToWrite, 
                                          writeLockTaken, localReaderCount, 
                                          localWriteIntent >>

rl_add_and_fetch2(self) == /\ pc[self] = "rl_add_and_fetch2"
                           /\ readers' = readers + 1
                           /\ pc' = [pc EXCEPT ![self] = "rl_check_slow_path"]
                           /\ UNCHANGED << intentToWrite, writeLockTaken, 
                                           localReaderCount, localWriteIntent >>

rl_critical_section(self) == /\ pc[self] = "rl_critical_section"
                             /\ TRUE
                             /\ pc' = [pc EXCEPT ![self] = "rl_unlock_shared2"]
                             /\ UNCHANGED << readers, intentToWrite, 
                                             writeLockTaken, localReaderCount, 
                                             localWriteIntent >>

rl_unlock_shared2(self) == /\ pc[self] = "rl_unlock_shared2"
                           /\ readers' = readers - 1
                           /\ pc' = [pc EXCEPT ![self] = "process_start"]
                           /\ UNCHANGED << intentToWrite, writeLockTaken, 
                                           localReaderCount, localWriteIntent >>

p(self) == process_start(self) \/ wl_take_mutex(self)
              \/ wl_set_intent(self) \/ wl_drain_readers(self)
              \/ wl_critical_section(self) \/ wl_remove_intent(self)
              \/ wl_release_mutex(self) \/ rl_add_and_fetch(self)
              \/ rl_check_slow_path(self) \/ rl_unlock_shared(self)
              \/ rl_drain_writers(self) \/ rl_add_and_fetch2(self)
              \/ rl_critical_section(self) \/ rl_unlock_shared2(self)

Next == (\E self \in Procs: p(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(p(self))

\* END TRANSLATION 

=============================================================================
