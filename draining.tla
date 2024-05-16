------------------------------ MODULE draining ------------------------------
EXTENDS Integers

CONSTANTS
MAX_WRITES,
THRESHOLD

ASSUME MAX_WRITES \in 1..1000
ASSUME THRESHOLD < MAX_WRITES



(*--algorithm draining {
variables 
    pendingWrites = 0;
    writesBlocked = FALSE;

define {

TypeOK ==   /\ pendingWrites <= MAX_WRITES
            /\ TRUE
}

fair process (driver = 1) 
variables
    modsSize = 0;
{
DRIVER_START:
while(TRUE) {
DRIVER_CLONING:
    while(~writesBlocked) {
DRIVER_TRANSFER_MODS:
        modsSize := pendingWrites;
        pendingWrites := 0;
DRIVER_ENTER_CS:
        if(modsSize < THRESHOLD) {
DRIVER_BLOCK_WRITES:
            writesBlocked := TRUE;
        }
    };
\* One last iteration of TRANSFER_MODS
DRIVER_LAST_TRANSFER_MODS:
    pendingWrites := 0;
DRIVER_UNBLOCK_WRITES:
    writesBlocked := FALSE;
}
}


fair process (writer = 2) {
WRITER_START: 
while(TRUE) {
    await(pendingWrites < MAX_WRITES);
WRITER_WRITE:
    await(~writesBlocked);
    pendingWrites := pendingWrites + 1;
}
}


} *)
\* BEGIN TRANSLATION (chksum(pcal) = "8fc70db2" /\ chksum(tla) = "26cb4244")
VARIABLES pendingWrites, writesBlocked, pc

(* define statement *)
TypeOK ==   /\ pendingWrites <= MAX_WRITES
            /\ TRUE

VARIABLE modsSize

vars == << pendingWrites, writesBlocked, pc, modsSize >>

ProcSet == {1} \cup {2}

Init == (* Global variables *)
        /\ pendingWrites = 0
        /\ writesBlocked = FALSE
        (* Process driver *)
        /\ modsSize = 0
        /\ pc = [self \in ProcSet |-> CASE self = 1 -> "DRIVER_START"
                                        [] self = 2 -> "WRITER_START"]

DRIVER_START == /\ pc[1] = "DRIVER_START"
                /\ pc' = [pc EXCEPT ![1] = "DRIVER_CLONING"]
                /\ UNCHANGED << pendingWrites, writesBlocked, modsSize >>

DRIVER_CLONING == /\ pc[1] = "DRIVER_CLONING"
                  /\ IF ~writesBlocked
                        THEN /\ pc' = [pc EXCEPT ![1] = "DRIVER_TRANSFER_MODS"]
                        ELSE /\ pc' = [pc EXCEPT ![1] = "DRIVER_LAST_TRANSFER_MODS"]
                  /\ UNCHANGED << pendingWrites, writesBlocked, modsSize >>

DRIVER_TRANSFER_MODS == /\ pc[1] = "DRIVER_TRANSFER_MODS"
                        /\ modsSize' = pendingWrites
                        /\ pendingWrites' = 0
                        /\ pc' = [pc EXCEPT ![1] = "DRIVER_ENTER_CS"]
                        /\ UNCHANGED writesBlocked

DRIVER_ENTER_CS == /\ pc[1] = "DRIVER_ENTER_CS"
                   /\ IF modsSize < THRESHOLD
                         THEN /\ pc' = [pc EXCEPT ![1] = "DRIVER_BLOCK_WRITES"]
                         ELSE /\ pc' = [pc EXCEPT ![1] = "DRIVER_CLONING"]
                   /\ UNCHANGED << pendingWrites, writesBlocked, modsSize >>

DRIVER_BLOCK_WRITES == /\ pc[1] = "DRIVER_BLOCK_WRITES"
                       /\ writesBlocked' = TRUE
                       /\ pc' = [pc EXCEPT ![1] = "DRIVER_CLONING"]
                       /\ UNCHANGED << pendingWrites, modsSize >>

DRIVER_LAST_TRANSFER_MODS == /\ pc[1] = "DRIVER_LAST_TRANSFER_MODS"
                             /\ pendingWrites' = 0
                             /\ pc' = [pc EXCEPT ![1] = "DRIVER_UNBLOCK_WRITES"]
                             /\ UNCHANGED << writesBlocked, modsSize >>

DRIVER_UNBLOCK_WRITES == /\ pc[1] = "DRIVER_UNBLOCK_WRITES"
                         /\ writesBlocked' = FALSE
                         /\ pc' = [pc EXCEPT ![1] = "DRIVER_START"]
                         /\ UNCHANGED << pendingWrites, modsSize >>

driver == DRIVER_START \/ DRIVER_CLONING \/ DRIVER_TRANSFER_MODS
             \/ DRIVER_ENTER_CS \/ DRIVER_BLOCK_WRITES
             \/ DRIVER_LAST_TRANSFER_MODS \/ DRIVER_UNBLOCK_WRITES

WRITER_START == /\ pc[2] = "WRITER_START"
                /\ (pendingWrites < MAX_WRITES)
                /\ pc' = [pc EXCEPT ![2] = "WRITER_WRITE"]
                /\ UNCHANGED << pendingWrites, writesBlocked, modsSize >>

WRITER_WRITE == /\ pc[2] = "WRITER_WRITE"
                /\ (~writesBlocked)
                /\ pendingWrites' = pendingWrites + 1
                /\ pc' = [pc EXCEPT ![2] = "WRITER_START"]
                /\ UNCHANGED << writesBlocked, modsSize >>

writer == WRITER_START \/ WRITER_WRITE

Next == driver \/ writer

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(driver)
        /\ WF_vars(writer)

\* END TRANSLATION 
=============================================================================
\* Modification History
\* Last modified Thu May 16 09:06:20 CEST 2024 by dgomezferro
\* Created Wed May 15 14:17:17 CEST 2024 by dgomezferro
