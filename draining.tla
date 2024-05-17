------------------------------ MODULE draining ------------------------------
EXTENDS Integers, TLC, Sequences, FiniteSets

CONSTANTS
MAX_WRITES,
THRESHOLD,
DOCS,
MAX_CHUNKS,
MAX_VALUES,
SHARDS,
DRIVERS,
WRITERS

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
    moveInProgress = [x \in chunks |-> FALSE ]; \* whether chunk is being moved
    ownership \in [chunks -> SHARDS]; \* What shard owns which chunk
    shardDocs = [x \in SHARDS |-> [y \in Docs |-> 0]]; \* local view of data in each shard

define {

TypeOK ==   /\ \A c \in chunks : Len(pendingWrites[c]) <= MAX_WRITES
            /\ \A c \in chunks : writesBlocked[c] \in {TRUE, FALSE}
            /\ \A c \in chunks : moveInProgress[c] \in {TRUE, FALSE}
            /\ \A c \in chunks : ownership[c] \in SHARDS
            /\ \A d \in Docs : allDocs[d] \in Values
            /\ \A s \in SHARDS, d \in Docs : shardDocs[s][d] \in Values
            
\* Map doc to chunk
DocToChunk(d) == CHOOSE c \in chunks : d \in c

\* Create write record from a <<key,value>> tuple
Write(w) == [ key |-> w[1], value |-> w[2] ]

NotInProgressChunks == {x \in chunks: ~moveInProgress[x]} 

Consistent == \A d \in Docs : allDocs[d] = shardDocs[ownership[DocToChunk(d)]][d]

}

\* Transfers a sequence of writes to the destination shard 
\*procedure transferMods(mods, destShard) 
\*variables i = 1;
\*{
\*TRANSFER_MODS:
\*    while (i <= Len(mods)) {
\*        shardDocs[destShard][mods[i].key] := mods[i].value;
\*        i := i+1;
\*    };
\*    return;
\*}

fair process (driver \in DRIVERS) 
variables
    chunkToMove = {};
    mods = <<>>;
    sourceShard = 0;
    destShard = 0;
    docsToCopy = {};
    i = 0;
{
DRIVER_START:
while(TRUE) {
DRIVER_PICK_CHUNK:
    with (pickedChunk \in NotInProgressChunks) {
        chunkToMove := pickedChunk;
    };
    moveInProgress[chunkToMove] := TRUE;
    sourceShard := ownership[chunkToMove];
DRIVER_PICK_SHARD:
    with (pickedShard \in (SHARDS \ {sourceShard})) {
        destShard := pickedShard;
    };
DRIVER_START_MOVE:
    docsToCopy := chunkToMove;
DRIVER_CLONING:
    while(docsToCopy /= {}) {
        with (doc \in docsToCopy) {
            docsToCopy := docsToCopy \ {doc};
            shardDocs[destShard][doc] := shardDocs[sourceShard][doc];
        }
    };
DRIVER_CATCHUP:
    while(~writesBlocked[chunkToMove]) {
DRIVER_COMPUTE_MODS:
        i:=1;
        mods := pendingWrites[chunkToMove];
        pendingWrites[chunkToMove] := <<>>;
        if(Len(mods) < THRESHOLD) {
DRIVER_BLOCK_WRITES:
            writesBlocked[chunkToMove] := TRUE;
        };
DRIVER_TRANSFER_MODS:
        while (i <= Len(mods)) {
            shardDocs[destShard][mods[i].key] := mods[i].value;
            i := i+1;
        };
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
    moveInProgress[chunkToMove] := FALSE;
    ownership[chunkToMove] := destShard;
    writesBlocked[chunkToMove] := FALSE;
}
}


fair process (writer \in WRITERS) 
variables
    write = [key|->0];
    writeSuccesful = FALSE;
    targetChunk = {};
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
WRITER_WRITE:
        await(Len(pendingWrites[targetChunk]) < MAX_WRITES);
        await(~writesBlocked[targetChunk]);
        if (ownership[targetChunk] = targetShard) {
            writeSuccesful := TRUE;
            allDocs[write.key] := write.value;
            shardDocs[targetShard][write.key] := write.value;
            if (moveInProgress[targetChunk]) {
                pendingWrites[targetChunk] := Append(pendingWrites[targetChunk], write);
            }
        }
    }
}
}


} *)
\* BEGIN TRANSLATION (chksum(pcal) = "9974396f" /\ chksum(tla) = "e6a4ca2d")
VARIABLES allDocs, chunks, pendingWrites, writesBlocked, moveInProgress, 
          ownership, shardDocs, pc

(* define statement *)
TypeOK ==   /\ \A c \in chunks : Len(pendingWrites[c]) <= MAX_WRITES
            /\ \A c \in chunks : writesBlocked[c] \in {TRUE, FALSE}
            /\ \A c \in chunks : moveInProgress[c] \in {TRUE, FALSE}
            /\ \A c \in chunks : ownership[c] \in SHARDS
            /\ \A d \in Docs : allDocs[d] \in Values
            /\ \A s \in SHARDS, d \in Docs : shardDocs[s][d] \in Values


DocToChunk(d) == CHOOSE c \in chunks : d \in c


Write(w) == [ key |-> w[1], value |-> w[2] ]

NotInProgressChunks == {x \in chunks: ~moveInProgress[x]}

Consistent == \A d \in Docs : allDocs[d] = shardDocs[ownership[DocToChunk(d)]][d]

VARIABLES chunkToMove, mods, sourceShard, destShard, docsToCopy, i, write, 
          writeSuccesful, targetChunk, targetShard

vars == << allDocs, chunks, pendingWrites, writesBlocked, moveInProgress, 
           ownership, shardDocs, pc, chunkToMove, mods, sourceShard, 
           destShard, docsToCopy, i, write, writeSuccesful, targetChunk, 
           targetShard >>

ProcSet == (DRIVERS) \cup (WRITERS)

Init == (* Global variables *)
        /\ allDocs = [x \in Docs |-> 0]
        /\ chunks \in BoundedPartitions(Docs, 2, MAX_CHUNKS)
        /\ pendingWrites = [x \in chunks |-> <<>> ]
        /\ writesBlocked = [x \in chunks |-> FALSE ]
        /\ moveInProgress = [x \in chunks |-> FALSE ]
        /\ ownership \in [chunks -> SHARDS]
        /\ shardDocs = [x \in SHARDS |-> [y \in Docs |-> 0]]
        (* Process driver *)
        /\ chunkToMove = [self \in DRIVERS |-> 0]
        /\ mods = [self \in DRIVERS |-> 0]
        /\ sourceShard = [self \in DRIVERS |-> 0]
        /\ destShard = [self \in DRIVERS |-> 0]
        /\ docsToCopy = [self \in DRIVERS |-> {}]
        /\ i = [self \in DRIVERS |-> 0]
        (* Process writer *)
        /\ write = [self \in WRITERS |-> 0]
        /\ writeSuccesful = [self \in WRITERS |-> FALSE]
        /\ targetChunk = [self \in WRITERS |-> 0]
        /\ targetShard = [self \in WRITERS |-> 0]
        /\ pc = [self \in ProcSet |-> CASE self \in DRIVERS -> "DRIVER_START"
                                        [] self \in WRITERS -> "WRITER_START"]

DRIVER_START(self) == /\ pc[self] = "DRIVER_START"
                      /\ pc' = [pc EXCEPT ![self] = "DRIVER_PICK_CHUNK"]
                      /\ UNCHANGED << allDocs, chunks, pendingWrites, 
                                      writesBlocked, moveInProgress, ownership, 
                                      shardDocs, chunkToMove, mods, 
                                      sourceShard, destShard, docsToCopy, i, 
                                      write, writeSuccesful, targetChunk, 
                                      targetShard >>

DRIVER_PICK_CHUNK(self) == /\ pc[self] = "DRIVER_PICK_CHUNK"
                           /\ \E pickedChunk \in NotInProgressChunks:
                                chunkToMove' = [chunkToMove EXCEPT ![self] = pickedChunk]
                           /\ moveInProgress' = [moveInProgress EXCEPT ![chunkToMove'[self]] = TRUE]
                           /\ sourceShard' = [sourceShard EXCEPT ![self] = ownership[chunkToMove'[self]]]
                           /\ pc' = [pc EXCEPT ![self] = "DRIVER_PICK_SHARD"]
                           /\ UNCHANGED << allDocs, chunks, pendingWrites, 
                                           writesBlocked, ownership, shardDocs, 
                                           mods, destShard, docsToCopy, i, 
                                           write, writeSuccesful, targetChunk, 
                                           targetShard >>

DRIVER_PICK_SHARD(self) == /\ pc[self] = "DRIVER_PICK_SHARD"
                           /\ \E pickedShard \in (SHARDS \ {sourceShard[self]}):
                                destShard' = [destShard EXCEPT ![self] = pickedShard]
                           /\ pc' = [pc EXCEPT ![self] = "DRIVER_START_MOVE"]
                           /\ UNCHANGED << allDocs, chunks, pendingWrites, 
                                           writesBlocked, moveInProgress, 
                                           ownership, shardDocs, chunkToMove, 
                                           mods, sourceShard, docsToCopy, i, 
                                           write, writeSuccesful, targetChunk, 
                                           targetShard >>

DRIVER_START_MOVE(self) == /\ pc[self] = "DRIVER_START_MOVE"
                           /\ docsToCopy' = [docsToCopy EXCEPT ![self] = chunkToMove[self]]
                           /\ pc' = [pc EXCEPT ![self] = "DRIVER_CLONING"]
                           /\ UNCHANGED << allDocs, chunks, pendingWrites, 
                                           writesBlocked, moveInProgress, 
                                           ownership, shardDocs, chunkToMove, 
                                           mods, sourceShard, destShard, i, 
                                           write, writeSuccesful, targetChunk, 
                                           targetShard >>

DRIVER_CLONING(self) == /\ pc[self] = "DRIVER_CLONING"
                        /\ IF docsToCopy[self] /= {}
                              THEN /\ \E doc \in docsToCopy[self]:
                                        /\ docsToCopy' = [docsToCopy EXCEPT ![self] = docsToCopy[self] \ {doc}]
                                        /\ shardDocs' = [shardDocs EXCEPT ![destShard[self]][doc] = shardDocs[sourceShard[self]][doc]]
                                   /\ pc' = [pc EXCEPT ![self] = "DRIVER_CLONING"]
                              ELSE /\ pc' = [pc EXCEPT ![self] = "DRIVER_CATCHUP"]
                                   /\ UNCHANGED << shardDocs, docsToCopy >>
                        /\ UNCHANGED << allDocs, chunks, pendingWrites, 
                                        writesBlocked, moveInProgress, 
                                        ownership, chunkToMove, mods, 
                                        sourceShard, destShard, i, write, 
                                        writeSuccesful, targetChunk, 
                                        targetShard >>

DRIVER_CATCHUP(self) == /\ pc[self] = "DRIVER_CATCHUP"
                        /\ IF ~writesBlocked[chunkToMove[self]]
                              THEN /\ pc' = [pc EXCEPT ![self] = "DRIVER_COMPUTE_MODS"]
                              ELSE /\ pc' = [pc EXCEPT ![self] = "DRIVER_LAST_COMPUTE_MODS"]
                        /\ UNCHANGED << allDocs, chunks, pendingWrites, 
                                        writesBlocked, moveInProgress, 
                                        ownership, shardDocs, chunkToMove, 
                                        mods, sourceShard, destShard, 
                                        docsToCopy, i, write, writeSuccesful, 
                                        targetChunk, targetShard >>

DRIVER_COMPUTE_MODS(self) == /\ pc[self] = "DRIVER_COMPUTE_MODS"
                             /\ i' = [i EXCEPT ![self] = 1]
                             /\ mods' = [mods EXCEPT ![self] = pendingWrites[chunkToMove[self]]]
                             /\ pendingWrites' = [pendingWrites EXCEPT ![chunkToMove[self]] = <<>>]
                             /\ IF Len(mods'[self]) < THRESHOLD
                                   THEN /\ pc' = [pc EXCEPT ![self] = "DRIVER_BLOCK_WRITES"]
                                   ELSE /\ pc' = [pc EXCEPT ![self] = "DRIVER_TRANSFER_MODS"]
                             /\ UNCHANGED << allDocs, chunks, writesBlocked, 
                                             moveInProgress, ownership, 
                                             shardDocs, chunkToMove, 
                                             sourceShard, destShard, 
                                             docsToCopy, write, writeSuccesful, 
                                             targetChunk, targetShard >>

DRIVER_BLOCK_WRITES(self) == /\ pc[self] = "DRIVER_BLOCK_WRITES"
                             /\ writesBlocked' = [writesBlocked EXCEPT ![chunkToMove[self]] = TRUE]
                             /\ pc' = [pc EXCEPT ![self] = "DRIVER_TRANSFER_MODS"]
                             /\ UNCHANGED << allDocs, chunks, pendingWrites, 
                                             moveInProgress, ownership, 
                                             shardDocs, chunkToMove, mods, 
                                             sourceShard, destShard, 
                                             docsToCopy, i, write, 
                                             writeSuccesful, targetChunk, 
                                             targetShard >>

DRIVER_TRANSFER_MODS(self) == /\ pc[self] = "DRIVER_TRANSFER_MODS"
                              /\ IF i[self] <= Len(mods[self])
                                    THEN /\ shardDocs' = [shardDocs EXCEPT ![destShard[self]][mods[self][i[self]].key] = mods[self][i[self]].value]
                                         /\ i' = [i EXCEPT ![self] = i[self]+1]
                                         /\ pc' = [pc EXCEPT ![self] = "DRIVER_TRANSFER_MODS"]
                                    ELSE /\ pc' = [pc EXCEPT ![self] = "DRIVER_CATCHUP"]
                                         /\ UNCHANGED << shardDocs, i >>
                              /\ UNCHANGED << allDocs, chunks, pendingWrites, 
                                              writesBlocked, moveInProgress, 
                                              ownership, chunkToMove, mods, 
                                              sourceShard, destShard, 
                                              docsToCopy, write, 
                                              writeSuccesful, targetChunk, 
                                              targetShard >>

DRIVER_LAST_COMPUTE_MODS(self) == /\ pc[self] = "DRIVER_LAST_COMPUTE_MODS"
                                  /\ mods' = [mods EXCEPT ![self] = pendingWrites[chunkToMove[self]]]
                                  /\ pendingWrites' = [pendingWrites EXCEPT ![chunkToMove[self]] = <<>>]
                                  /\ i' = [i EXCEPT ![self] = 1]
                                  /\ pc' = [pc EXCEPT ![self] = "DRIVER_LAST_TRANSFER_MODS"]
                                  /\ UNCHANGED << allDocs, chunks, 
                                                  writesBlocked, 
                                                  moveInProgress, ownership, 
                                                  shardDocs, chunkToMove, 
                                                  sourceShard, destShard, 
                                                  docsToCopy, write, 
                                                  writeSuccesful, targetChunk, 
                                                  targetShard >>

DRIVER_LAST_TRANSFER_MODS(self) == /\ pc[self] = "DRIVER_LAST_TRANSFER_MODS"
                                   /\ IF i[self] <= Len(mods[self])
                                         THEN /\ shardDocs' = [shardDocs EXCEPT ![destShard[self]][mods[self][i[self]].key] = mods[self][i[self]].value]
                                              /\ i' = [i EXCEPT ![self] = i[self]+1]
                                              /\ pc' = [pc EXCEPT ![self] = "DRIVER_LAST_TRANSFER_MODS"]
                                         ELSE /\ pc' = [pc EXCEPT ![self] = "DRIVER_COMMIT_MOVE"]
                                              /\ UNCHANGED << shardDocs, i >>
                                   /\ UNCHANGED << allDocs, chunks, 
                                                   pendingWrites, 
                                                   writesBlocked, 
                                                   moveInProgress, ownership, 
                                                   chunkToMove, mods, 
                                                   sourceShard, destShard, 
                                                   docsToCopy, write, 
                                                   writeSuccesful, targetChunk, 
                                                   targetShard >>

DRIVER_COMMIT_MOVE(self) == /\ pc[self] = "DRIVER_COMMIT_MOVE"
                            /\ moveInProgress' = [moveInProgress EXCEPT ![chunkToMove[self]] = FALSE]
                            /\ ownership' = [ownership EXCEPT ![chunkToMove[self]] = destShard[self]]
                            /\ writesBlocked' = [writesBlocked EXCEPT ![chunkToMove[self]] = FALSE]
                            /\ pc' = [pc EXCEPT ![self] = "DRIVER_START"]
                            /\ UNCHANGED << allDocs, chunks, pendingWrites, 
                                            shardDocs, chunkToMove, mods, 
                                            sourceShard, destShard, docsToCopy, 
                                            i, write, writeSuccesful, 
                                            targetChunk, targetShard >>

driver(self) == DRIVER_START(self) \/ DRIVER_PICK_CHUNK(self)
                   \/ DRIVER_PICK_SHARD(self) \/ DRIVER_START_MOVE(self)
                   \/ DRIVER_CLONING(self) \/ DRIVER_CATCHUP(self)
                   \/ DRIVER_COMPUTE_MODS(self)
                   \/ DRIVER_BLOCK_WRITES(self)
                   \/ DRIVER_TRANSFER_MODS(self)
                   \/ DRIVER_LAST_COMPUTE_MODS(self)
                   \/ DRIVER_LAST_TRANSFER_MODS(self)
                   \/ DRIVER_COMMIT_MOVE(self)

WRITER_START(self) == /\ pc[self] = "WRITER_START"
                      /\ writeSuccesful' = [writeSuccesful EXCEPT ![self] = FALSE]
                      /\ \E pickedWrite \in (Docs \X Values):
                           write' = [write EXCEPT ![self] = Write(pickedWrite)]
                      /\ pc' = [pc EXCEPT ![self] = "WRITER_TRY_WRITE"]
                      /\ UNCHANGED << allDocs, chunks, pendingWrites, 
                                      writesBlocked, moveInProgress, ownership, 
                                      shardDocs, chunkToMove, mods, 
                                      sourceShard, destShard, docsToCopy, i, 
                                      targetChunk, targetShard >>

WRITER_TRY_WRITE(self) == /\ pc[self] = "WRITER_TRY_WRITE"
                          /\ IF ~writeSuccesful[self]
                                THEN /\ targetChunk' = [targetChunk EXCEPT ![self] = DocToChunk(write[self].key)]
                                     /\ targetShard' = [targetShard EXCEPT ![self] = ownership[targetChunk'[self]]]
                                     /\ pc' = [pc EXCEPT ![self] = "WRITER_WRITE"]
                                ELSE /\ pc' = [pc EXCEPT ![self] = "WRITER_START"]
                                     /\ UNCHANGED << targetChunk, targetShard >>
                          /\ UNCHANGED << allDocs, chunks, pendingWrites, 
                                          writesBlocked, moveInProgress, 
                                          ownership, shardDocs, chunkToMove, 
                                          mods, sourceShard, destShard, 
                                          docsToCopy, i, write, writeSuccesful >>

WRITER_WRITE(self) == /\ pc[self] = "WRITER_WRITE"
                      /\ (Len(pendingWrites[targetChunk[self]]) < MAX_WRITES)
                      /\ (~writesBlocked[targetChunk[self]])
                      /\ IF ownership[targetChunk[self]] = targetShard[self]
                            THEN /\ writeSuccesful' = [writeSuccesful EXCEPT ![self] = TRUE]
                                 /\ allDocs' = [allDocs EXCEPT ![write[self].key] = write[self].value]
                                 /\ shardDocs' = [shardDocs EXCEPT ![targetShard[self]][write[self].key] = write[self].value]
                                 /\ IF moveInProgress[targetChunk[self]]
                                       THEN /\ pendingWrites' = [pendingWrites EXCEPT ![targetChunk[self]] = Append(pendingWrites[targetChunk[self]], write[self])]
                                       ELSE /\ TRUE
                                            /\ UNCHANGED pendingWrites
                            ELSE /\ TRUE
                                 /\ UNCHANGED << allDocs, pendingWrites, 
                                                 shardDocs, writeSuccesful >>
                      /\ pc' = [pc EXCEPT ![self] = "WRITER_TRY_WRITE"]
                      /\ UNCHANGED << chunks, writesBlocked, moveInProgress, 
                                      ownership, chunkToMove, mods, 
                                      sourceShard, destShard, docsToCopy, i, 
                                      write, targetChunk, targetShard >>

writer(self) == WRITER_START(self) \/ WRITER_TRY_WRITE(self)
                   \/ WRITER_WRITE(self)

Next == (\E self \in DRIVERS: driver(self))
           \/ (\E self \in WRITERS: writer(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in DRIVERS : WF_vars(driver(self))
        /\ \A self \in WRITERS : WF_vars(writer(self))

\* END TRANSLATION 
=============================================================================
\* Modification History
\* Last modified Thu May 16 19:13:42 CEST 2024 by dgomezferro
\* Created Wed May 15 14:17:17 CEST 2024 by dgomezferro
