------------------------------ MODULE draining ------------------------------
EXTENDS Integers, TLC, Sequences, FiniteSets

CONSTANTS
MAX_WRITES,
THRESHOLD,
DOCS,
MAX_CHUNKS,
MAX_VALUES,
SHARDS

ASSUME MAX_WRITES \in 1..1000
ASSUME THRESHOLD <= MAX_WRITES
\*ASSUME MAX_DOCS \in 2..100
ASSUME MAX_CHUNKS \in 2..Cardinality(DOCS)
ASSUME MAX_VALUES \in 1..10

\* From https://learntla.com/examples/partitions.html 
PartitionsV1(set) ==
  LET F == [set -> 1..Cardinality(set)]
    G(f) == [i \in 1..Cardinality(set) |-> {x \in set: f[x] = i}]
  IN
    {G(f): f \in F}

Range(f) == {f[x] : x \in DOMAIN f}

Partitions(set) ==
    {Range(P) \ {{}}: P \in PartitionsV1(set)}
\* From https://learntla.com/examples/partitions.html 

BoundedPartitions(set, min, max) == {x \in Partitions(set) : Cardinality(x) >= min /\ Cardinality(x) <= max}

Docs == DOCS
Values == 0..MAX_VALUES


(*--algorithm draining {
variables 
    allDocs = [x \in Docs |-> 0]; \* global view of the data
    chunks \in BoundedPartitions(Docs, 2, MAX_CHUNKS); \* try all chunk arrangmenets with at least 2 chunks and no more than MAX_CHUNKS
    pendingWrites = [x \in chunks |-> <<>> ]; \* pending writes on each chunk
    writesBlocked = [x \in chunks |-> FALSE ]; \* whether writes are blocked on each chunk
    ownership \in [chunks -> SHARDS]; \* What shard owns which chunk
    shardDocs = [x \in SHARDS |-> [y \in Docs |-> 0]]; \* local view of data in each shard

define {

TypeOK ==   /\ \A c \in chunks : Len(pendingWrites[c]) <= MAX_WRITES
            /\ \A c \in chunks : writesBlocked[c] = TRUE \/ writesBlocked[c] = FALSE
            
\* Map doc to chunk
DocToChunk(d) == CHOOSE c \in chunks : d \in c

\* Create write record from a <<key,value>> tuple
Write(w) == [ key |-> w[1], value |-> w[2] ]

Consistent == \A d \in Docs : allDocs[d] = shardDocs[ownership[DocToChunk(d)]][d]

}

fair process (driver = 1) 
variables
    chunkToMove = 0;
    mods = 0;
    sourceShard = 0;
    destShard = 0;
    i = 0;
    mod = 0;
{
DRIVER_START:
while(TRUE) {
DRIVER_PICK_CHUNK:
    with (pickedChunk \in chunks) {
        chunkToMove := pickedChunk;
    };
    sourceShard := ownership[chunkToMove];
DRIVER_PICK_SHARD:
    with (pickedShard \in (SHARDS \ {sourceShard})) {
        destShard := pickedShard;
    };
DRIVER_CLONING:
    while(~writesBlocked[chunkToMove]) {
DRIVER_COMPUTE_MODS:
        mods := pendingWrites[chunkToMove];
        pendingWrites[chunkToMove] := <<>>;
DRIVER_ENTER_CS:
        if(Len(mods) < THRESHOLD) {
DRIVER_BLOCK_WRITES:
            writesBlocked[chunkToMove] := TRUE;
        };
DRIVER_ABOUT_TO_TRANSFER_MODS:
        i := 1;
DRIVER_TRANSFER_MODS:
        while (i <= Len(mods)) {
            shardDocs[destShard][mods[i].key] := mods[i].value;
            i := i+1;
        }
    };
\* One last iteration of TRANSFER_MODS
DRIVER_LAST_COMPUTE_MODS:
    mods := pendingWrites[chunkToMove];
    pendingWrites[chunkToMove] := <<>>;
    i := 1;
DRIVER_LAST_TRANSFER_MODS:
    while (i <= Len(mods)) {
        shardDocs[destShard][mods[i].key] := mods[i].value;
        i := i+1;
    };
DRIVER_COMMIT_MOVE:
    ownership[chunkToMove] := destShard;
DRIVER_UNBLOCK_WRITES:
    writesBlocked[chunkToMove] := FALSE;
}
}


fair process (writer = 2) 
variables
    write = 0;
    writeSuccesful = FALSE;
    targetChunk = 0;
    targetShard = 0;
{
WRITER_START: 
while(TRUE) {
    writeSuccesful := FALSE;
    with (pickedWrite \in (Docs \X Values)) {
        write := Write(pickedWrite);
    };
WRITER_TRY_WRITE:
    while(~writeSuccesful) {
        targetChunk := DocToChunk(write.key);
        targetShard := ownership[targetChunk];
        await(Len(pendingWrites[targetChunk]) < MAX_WRITES);
WRITER_WRITE:
        await(~writesBlocked[targetChunk]);
        if (ownership[targetChunk] = targetShard) {
            writeSuccesful := TRUE;
            allDocs[write.key] := write.value;
            shardDocs[targetShard][write.key] := write.value;
            pendingWrites[targetChunk] := Append(pendingWrites[targetChunk], write);
        }
    }
}
}


} *)
\* BEGIN TRANSLATION (chksum(pcal) = "34115dec" /\ chksum(tla) = "bfa65b4e")
VARIABLES allDocs, chunks, pendingWrites, writesBlocked, ownership, shardDocs, 
          pc

(* define statement *)
TypeOK ==   /\ \A c \in chunks : Len(pendingWrites[c]) <= MAX_WRITES
            /\ \A c \in chunks : writesBlocked[c] = TRUE \/ writesBlocked[c] = FALSE


DocToChunk(d) == CHOOSE c \in chunks : d \in c


Write(w) == [ key |-> w[1], value |-> w[2] ]

Consistent == \A d \in Docs : allDocs[d] = shardDocs[ownership[DocToChunk(d)]][d]

VARIABLES chunkToMove, mods, sourceShard, destShard, i, mod, write, 
          writeSuccesful, targetChunk, targetShard

vars == << allDocs, chunks, pendingWrites, writesBlocked, ownership, 
           shardDocs, pc, chunkToMove, mods, sourceShard, destShard, i, mod, 
           write, writeSuccesful, targetChunk, targetShard >>

ProcSet == {1} \cup {2}

Init == (* Global variables *)
        /\ allDocs = [x \in Docs |-> 0]
        /\ chunks \in BoundedPartitions(Docs, 2, MAX_CHUNKS)
        /\ pendingWrites = [x \in chunks |-> <<>> ]
        /\ writesBlocked = [x \in chunks |-> FALSE ]
        /\ ownership \in [chunks -> SHARDS]
        /\ shardDocs = [x \in SHARDS |-> [y \in Docs |-> 0]]
        (* Process driver *)
        /\ chunkToMove = 0
        /\ mods = 0
        /\ sourceShard = 0
        /\ destShard = 0
        /\ i = 0
        /\ mod = 0
        (* Process writer *)
        /\ write = 0
        /\ writeSuccesful = FALSE
        /\ targetChunk = 0
        /\ targetShard = 0
        /\ pc = [self \in ProcSet |-> CASE self = 1 -> "DRIVER_START"
                                        [] self = 2 -> "WRITER_START"]

DRIVER_START == /\ pc[1] = "DRIVER_START"
                /\ pc' = [pc EXCEPT ![1] = "DRIVER_PICK_CHUNK"]
                /\ UNCHANGED << allDocs, chunks, pendingWrites, writesBlocked, 
                                ownership, shardDocs, chunkToMove, mods, 
                                sourceShard, destShard, i, mod, write, 
                                writeSuccesful, targetChunk, targetShard >>

DRIVER_PICK_CHUNK == /\ pc[1] = "DRIVER_PICK_CHUNK"
                     /\ \E pickedChunk \in chunks:
                          chunkToMove' = pickedChunk
                     /\ sourceShard' = ownership[chunkToMove']
                     /\ pc' = [pc EXCEPT ![1] = "DRIVER_PICK_SHARD"]
                     /\ UNCHANGED << allDocs, chunks, pendingWrites, 
                                     writesBlocked, ownership, shardDocs, mods, 
                                     destShard, i, mod, write, writeSuccesful, 
                                     targetChunk, targetShard >>

DRIVER_PICK_SHARD == /\ pc[1] = "DRIVER_PICK_SHARD"
                     /\ \E pickedShard \in (SHARDS \ {sourceShard}):
                          destShard' = pickedShard
                     /\ pc' = [pc EXCEPT ![1] = "DRIVER_CLONING"]
                     /\ UNCHANGED << allDocs, chunks, pendingWrites, 
                                     writesBlocked, ownership, shardDocs, 
                                     chunkToMove, mods, sourceShard, i, mod, 
                                     write, writeSuccesful, targetChunk, 
                                     targetShard >>

DRIVER_CLONING == /\ pc[1] = "DRIVER_CLONING"
                  /\ IF ~writesBlocked[chunkToMove]
                        THEN /\ pc' = [pc EXCEPT ![1] = "DRIVER_COMPUTE_MODS"]
                        ELSE /\ pc' = [pc EXCEPT ![1] = "DRIVER_LAST_COMPUTE_MODS"]
                  /\ UNCHANGED << allDocs, chunks, pendingWrites, 
                                  writesBlocked, ownership, shardDocs, 
                                  chunkToMove, mods, sourceShard, destShard, i, 
                                  mod, write, writeSuccesful, targetChunk, 
                                  targetShard >>

DRIVER_COMPUTE_MODS == /\ pc[1] = "DRIVER_COMPUTE_MODS"
                       /\ mods' = pendingWrites[chunkToMove]
                       /\ pendingWrites' = [pendingWrites EXCEPT ![chunkToMove] = <<>>]
                       /\ pc' = [pc EXCEPT ![1] = "DRIVER_ENTER_CS"]
                       /\ UNCHANGED << allDocs, chunks, writesBlocked, 
                                       ownership, shardDocs, chunkToMove, 
                                       sourceShard, destShard, i, mod, write, 
                                       writeSuccesful, targetChunk, 
                                       targetShard >>

DRIVER_ENTER_CS == /\ pc[1] = "DRIVER_ENTER_CS"
                   /\ IF Len(mods) < THRESHOLD
                         THEN /\ pc' = [pc EXCEPT ![1] = "DRIVER_BLOCK_WRITES"]
                         ELSE /\ pc' = [pc EXCEPT ![1] = "DRIVER_ABOUT_TO_TRANSFER_MODS"]
                   /\ UNCHANGED << allDocs, chunks, pendingWrites, 
                                   writesBlocked, ownership, shardDocs, 
                                   chunkToMove, mods, sourceShard, destShard, 
                                   i, mod, write, writeSuccesful, targetChunk, 
                                   targetShard >>

DRIVER_BLOCK_WRITES == /\ pc[1] = "DRIVER_BLOCK_WRITES"
                       /\ writesBlocked' = [writesBlocked EXCEPT ![chunkToMove] = TRUE]
                       /\ pc' = [pc EXCEPT ![1] = "DRIVER_ABOUT_TO_TRANSFER_MODS"]
                       /\ UNCHANGED << allDocs, chunks, pendingWrites, 
                                       ownership, shardDocs, chunkToMove, mods, 
                                       sourceShard, destShard, i, mod, write, 
                                       writeSuccesful, targetChunk, 
                                       targetShard >>

DRIVER_ABOUT_TO_TRANSFER_MODS == /\ pc[1] = "DRIVER_ABOUT_TO_TRANSFER_MODS"
                                 /\ i' = 1
                                 /\ pc' = [pc EXCEPT ![1] = "DRIVER_TRANSFER_MODS"]
                                 /\ UNCHANGED << allDocs, chunks, 
                                                 pendingWrites, writesBlocked, 
                                                 ownership, shardDocs, 
                                                 chunkToMove, mods, 
                                                 sourceShard, destShard, mod, 
                                                 write, writeSuccesful, 
                                                 targetChunk, targetShard >>

DRIVER_TRANSFER_MODS == /\ pc[1] = "DRIVER_TRANSFER_MODS"
                        /\ IF i <= Len(mods)
                              THEN /\ shardDocs' = [shardDocs EXCEPT ![destShard][mods[i].key] = mods[i].value]
                                   /\ i' = i+1
                                   /\ pc' = [pc EXCEPT ![1] = "DRIVER_TRANSFER_MODS"]
                              ELSE /\ pc' = [pc EXCEPT ![1] = "DRIVER_CLONING"]
                                   /\ UNCHANGED << shardDocs, i >>
                        /\ UNCHANGED << allDocs, chunks, pendingWrites, 
                                        writesBlocked, ownership, chunkToMove, 
                                        mods, sourceShard, destShard, mod, 
                                        write, writeSuccesful, targetChunk, 
                                        targetShard >>

DRIVER_LAST_COMPUTE_MODS == /\ pc[1] = "DRIVER_LAST_COMPUTE_MODS"
                            /\ mods' = pendingWrites[chunkToMove]
                            /\ pendingWrites' = [pendingWrites EXCEPT ![chunkToMove] = <<>>]
                            /\ i' = 1
                            /\ pc' = [pc EXCEPT ![1] = "DRIVER_LAST_TRANSFER_MODS"]
                            /\ UNCHANGED << allDocs, chunks, writesBlocked, 
                                            ownership, shardDocs, chunkToMove, 
                                            sourceShard, destShard, mod, write, 
                                            writeSuccesful, targetChunk, 
                                            targetShard >>

DRIVER_LAST_TRANSFER_MODS == /\ pc[1] = "DRIVER_LAST_TRANSFER_MODS"
                             /\ IF i <= Len(mods)
                                   THEN /\ shardDocs' = [shardDocs EXCEPT ![destShard][mods[i].key] = mods[i].value]
                                        /\ i' = i+1
                                        /\ pc' = [pc EXCEPT ![1] = "DRIVER_LAST_TRANSFER_MODS"]
                                   ELSE /\ pc' = [pc EXCEPT ![1] = "DRIVER_COMMIT_MOVE"]
                                        /\ UNCHANGED << shardDocs, i >>
                             /\ UNCHANGED << allDocs, chunks, pendingWrites, 
                                             writesBlocked, ownership, 
                                             chunkToMove, mods, sourceShard, 
                                             destShard, mod, write, 
                                             writeSuccesful, targetChunk, 
                                             targetShard >>

DRIVER_COMMIT_MOVE == /\ pc[1] = "DRIVER_COMMIT_MOVE"
                      /\ ownership' = [ownership EXCEPT ![chunkToMove] = destShard]
                      /\ pc' = [pc EXCEPT ![1] = "DRIVER_UNBLOCK_WRITES"]
                      /\ UNCHANGED << allDocs, chunks, pendingWrites, 
                                      writesBlocked, shardDocs, chunkToMove, 
                                      mods, sourceShard, destShard, i, mod, 
                                      write, writeSuccesful, targetChunk, 
                                      targetShard >>

DRIVER_UNBLOCK_WRITES == /\ pc[1] = "DRIVER_UNBLOCK_WRITES"
                         /\ writesBlocked' = [writesBlocked EXCEPT ![chunkToMove] = FALSE]
                         /\ pc' = [pc EXCEPT ![1] = "DRIVER_START"]
                         /\ UNCHANGED << allDocs, chunks, pendingWrites, 
                                         ownership, shardDocs, chunkToMove, 
                                         mods, sourceShard, destShard, i, mod, 
                                         write, writeSuccesful, targetChunk, 
                                         targetShard >>

driver == DRIVER_START \/ DRIVER_PICK_CHUNK \/ DRIVER_PICK_SHARD
             \/ DRIVER_CLONING \/ DRIVER_COMPUTE_MODS \/ DRIVER_ENTER_CS
             \/ DRIVER_BLOCK_WRITES \/ DRIVER_ABOUT_TO_TRANSFER_MODS
             \/ DRIVER_TRANSFER_MODS \/ DRIVER_LAST_COMPUTE_MODS
             \/ DRIVER_LAST_TRANSFER_MODS \/ DRIVER_COMMIT_MOVE
             \/ DRIVER_UNBLOCK_WRITES

WRITER_START == /\ pc[2] = "WRITER_START"
                /\ writeSuccesful' = FALSE
                /\ \E pickedWrite \in (Docs \X Values):
                     write' = Write(pickedWrite)
                /\ pc' = [pc EXCEPT ![2] = "WRITER_TRY_WRITE"]
                /\ UNCHANGED << allDocs, chunks, pendingWrites, writesBlocked, 
                                ownership, shardDocs, chunkToMove, mods, 
                                sourceShard, destShard, i, mod, targetChunk, 
                                targetShard >>

WRITER_TRY_WRITE == /\ pc[2] = "WRITER_TRY_WRITE"
                    /\ IF ~writeSuccesful
                          THEN /\ targetChunk' = DocToChunk(write.key)
                               /\ targetShard' = ownership[targetChunk']
                               /\ (Len(pendingWrites[targetChunk']) < MAX_WRITES)
                               /\ pc' = [pc EXCEPT ![2] = "WRITER_WRITE"]
                          ELSE /\ pc' = [pc EXCEPT ![2] = "WRITER_START"]
                               /\ UNCHANGED << targetChunk, targetShard >>
                    /\ UNCHANGED << allDocs, chunks, pendingWrites, 
                                    writesBlocked, ownership, shardDocs, 
                                    chunkToMove, mods, sourceShard, destShard, 
                                    i, mod, write, writeSuccesful >>

WRITER_WRITE == /\ pc[2] = "WRITER_WRITE"
                /\ (~writesBlocked[targetChunk])
                /\ IF ownership[targetChunk] = targetShard
                      THEN /\ writeSuccesful' = TRUE
                           /\ allDocs' = [allDocs EXCEPT ![write.key] = write.value]
                           /\ shardDocs' = [shardDocs EXCEPT ![targetShard][write.key] = write.value]
                           /\ pendingWrites' = [pendingWrites EXCEPT ![targetChunk] = Append(pendingWrites[targetChunk], write)]
                      ELSE /\ TRUE
                           /\ UNCHANGED << allDocs, pendingWrites, shardDocs, 
                                           writeSuccesful >>
                /\ pc' = [pc EXCEPT ![2] = "WRITER_TRY_WRITE"]
                /\ UNCHANGED << chunks, writesBlocked, ownership, chunkToMove, 
                                mods, sourceShard, destShard, i, mod, write, 
                                targetChunk, targetShard >>

writer == WRITER_START \/ WRITER_TRY_WRITE \/ WRITER_WRITE

Next == driver \/ writer

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(driver)
        /\ WF_vars(writer)

\* END TRANSLATION 
=============================================================================
\* Modification History
\* Last modified Thu May 16 13:58:28 CEST 2024 by dgomezferro
\* Created Wed May 15 14:17:17 CEST 2024 by dgomezferro
