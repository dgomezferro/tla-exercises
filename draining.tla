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

Consistent == \A d \in Docs : allDocs[d] = shardDocs[ownership[DocToChunk(d)]][d]



}

procedure transferMods(mods, destShard) 
variables i = 1;
{
TRANSFER_MODS:
    while (i <= Len(mods)) {
        shardDocs[destShard][mods[i].key] := mods[i].value;
        i := i+1;
    };
    return;
}

fair process (driver = 1) 
variables
    chunkToMove = 0;
    mods = 0;
    sourceShard = 0;
    destShard = 0;
    i = 0;
    mod = 0;
    docsToCopy = {};
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
DRIVER_START_MOVE:
    moveInProgress[chunkToMove] := TRUE;
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
        mods := pendingWrites[chunkToMove];
        pendingWrites[chunkToMove] := <<>>;
DRIVER_ENTER_CS:
        if(Len(mods) < THRESHOLD) {
DRIVER_BLOCK_WRITES:
            writesBlocked[chunkToMove] := TRUE;
        };
DRIVER_TRANSFER_MODS:
        call transferMods(mods, destShard);
    };
\* One last iteration of TRANSFER_MODS
DRIVER_LAST_COMPUTE_MODS:
    mods := pendingWrites[chunkToMove];
    pendingWrites[chunkToMove] := <<>>;
DRIVER_LAST_TRANSFER_MODS:
    call transferMods(mods, destShard);
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
\* BEGIN TRANSLATION (chksum(pcal) = "625c2c56" /\ chksum(tla) = "f9d247a8")
\* Process variable mods of process driver at line 82 col 5 changed to mods_
\* Process variable destShard of process driver at line 84 col 5 changed to destShard_
\* Process variable i of process driver at line 85 col 5 changed to i_
CONSTANT defaultInitValue
VARIABLES allDocs, chunks, pendingWrites, writesBlocked, moveInProgress, 
          ownership, shardDocs, pc, stack

(* define statement *)
TypeOK ==   /\ \A c \in chunks : Len(pendingWrites[c]) <= MAX_WRITES
            /\ \A c \in chunks : writesBlocked[c] \in {TRUE, FALSE}
            /\ \A c \in chunks : moveInProgress[c] \in {TRUE, FALSE}
            /\ \A c \in chunks : ownership[c] \in SHARDS
            /\ \A d \in Docs : allDocs[d] \in Values
            /\ \A s \in SHARDS, d \in Docs : shardDocs[s][d] \in Values


DocToChunk(d) == CHOOSE c \in chunks : d \in c


Write(w) == [ key |-> w[1], value |-> w[2] ]

Consistent == \A d \in Docs : allDocs[d] = shardDocs[ownership[DocToChunk(d)]][d]

VARIABLES mods, destShard, i, chunkToMove, mods_, sourceShard, destShard_, i_, 
          mod, docsToCopy, write, writeSuccesful, targetChunk, targetShard

vars == << allDocs, chunks, pendingWrites, writesBlocked, moveInProgress, 
           ownership, shardDocs, pc, stack, mods, destShard, i, chunkToMove, 
           mods_, sourceShard, destShard_, i_, mod, docsToCopy, write, 
           writeSuccesful, targetChunk, targetShard >>

ProcSet == {1} \cup {2}

Init == (* Global variables *)
        /\ allDocs = [x \in Docs |-> 0]
        /\ chunks \in BoundedPartitions(Docs, 2, MAX_CHUNKS)
        /\ pendingWrites = [x \in chunks |-> <<>> ]
        /\ writesBlocked = [x \in chunks |-> FALSE ]
        /\ moveInProgress = [x \in chunks |-> FALSE ]
        /\ ownership \in [chunks -> SHARDS]
        /\ shardDocs = [x \in SHARDS |-> [y \in Docs |-> 0]]
        (* Procedure transferMods *)
        /\ mods = [ self \in ProcSet |-> defaultInitValue]
        /\ destShard = [ self \in ProcSet |-> defaultInitValue]
        /\ i = [ self \in ProcSet |-> 1]
        (* Process driver *)
        /\ chunkToMove = 0
        /\ mods_ = 0
        /\ sourceShard = 0
        /\ destShard_ = 0
        /\ i_ = 0
        /\ mod = 0
        /\ docsToCopy = {}
        (* Process writer *)
        /\ write = 0
        /\ writeSuccesful = FALSE
        /\ targetChunk = 0
        /\ targetShard = 0
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self = 1 -> "DRIVER_START"
                                        [] self = 2 -> "WRITER_START"]

TRANSFER_MODS(self) == /\ pc[self] = "TRANSFER_MODS"
                       /\ IF i[self] <= Len(mods[self])
                             THEN /\ shardDocs' = [shardDocs EXCEPT ![destShard[self]][mods[self][i[self]].key] = mods[self][i[self]].value]
                                  /\ i' = [i EXCEPT ![self] = i[self]+1]
                                  /\ pc' = [pc EXCEPT ![self] = "TRANSFER_MODS"]
                                  /\ UNCHANGED << stack, mods, destShard >>
                             ELSE /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                  /\ i' = [i EXCEPT ![self] = Head(stack[self]).i]
                                  /\ mods' = [mods EXCEPT ![self] = Head(stack[self]).mods]
                                  /\ destShard' = [destShard EXCEPT ![self] = Head(stack[self]).destShard]
                                  /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                  /\ UNCHANGED shardDocs
                       /\ UNCHANGED << allDocs, chunks, pendingWrites, 
                                       writesBlocked, moveInProgress, 
                                       ownership, chunkToMove, mods_, 
                                       sourceShard, destShard_, i_, mod, 
                                       docsToCopy, write, writeSuccesful, 
                                       targetChunk, targetShard >>

transferMods(self) == TRANSFER_MODS(self)

DRIVER_START == /\ pc[1] = "DRIVER_START"
                /\ pc' = [pc EXCEPT ![1] = "DRIVER_PICK_CHUNK"]
                /\ UNCHANGED << allDocs, chunks, pendingWrites, writesBlocked, 
                                moveInProgress, ownership, shardDocs, stack, 
                                mods, destShard, i, chunkToMove, mods_, 
                                sourceShard, destShard_, i_, mod, docsToCopy, 
                                write, writeSuccesful, targetChunk, 
                                targetShard >>

DRIVER_PICK_CHUNK == /\ pc[1] = "DRIVER_PICK_CHUNK"
                     /\ \E pickedChunk \in chunks:
                          chunkToMove' = pickedChunk
                     /\ sourceShard' = ownership[chunkToMove']
                     /\ pc' = [pc EXCEPT ![1] = "DRIVER_PICK_SHARD"]
                     /\ UNCHANGED << allDocs, chunks, pendingWrites, 
                                     writesBlocked, moveInProgress, ownership, 
                                     shardDocs, stack, mods, destShard, i, 
                                     mods_, destShard_, i_, mod, docsToCopy, 
                                     write, writeSuccesful, targetChunk, 
                                     targetShard >>

DRIVER_PICK_SHARD == /\ pc[1] = "DRIVER_PICK_SHARD"
                     /\ \E pickedShard \in (SHARDS \ {sourceShard}):
                          destShard_' = pickedShard
                     /\ pc' = [pc EXCEPT ![1] = "DRIVER_START_MOVE"]
                     /\ UNCHANGED << allDocs, chunks, pendingWrites, 
                                     writesBlocked, moveInProgress, ownership, 
                                     shardDocs, stack, mods, destShard, i, 
                                     chunkToMove, mods_, sourceShard, i_, mod, 
                                     docsToCopy, write, writeSuccesful, 
                                     targetChunk, targetShard >>

DRIVER_START_MOVE == /\ pc[1] = "DRIVER_START_MOVE"
                     /\ moveInProgress' = [moveInProgress EXCEPT ![chunkToMove] = TRUE]
                     /\ docsToCopy' = chunkToMove
                     /\ pc' = [pc EXCEPT ![1] = "DRIVER_CLONING"]
                     /\ UNCHANGED << allDocs, chunks, pendingWrites, 
                                     writesBlocked, ownership, shardDocs, 
                                     stack, mods, destShard, i, chunkToMove, 
                                     mods_, sourceShard, destShard_, i_, mod, 
                                     write, writeSuccesful, targetChunk, 
                                     targetShard >>

DRIVER_CLONING == /\ pc[1] = "DRIVER_CLONING"
                  /\ IF docsToCopy /= {}
                        THEN /\ \E doc \in docsToCopy:
                                  /\ docsToCopy' = docsToCopy \ {doc}
                                  /\ shardDocs' = [shardDocs EXCEPT ![destShard_][doc] = shardDocs[sourceShard][doc]]
                             /\ pc' = [pc EXCEPT ![1] = "DRIVER_CLONING"]
                        ELSE /\ pc' = [pc EXCEPT ![1] = "DRIVER_CATCHUP"]
                             /\ UNCHANGED << shardDocs, docsToCopy >>
                  /\ UNCHANGED << allDocs, chunks, pendingWrites, 
                                  writesBlocked, moveInProgress, ownership, 
                                  stack, mods, destShard, i, chunkToMove, 
                                  mods_, sourceShard, destShard_, i_, mod, 
                                  write, writeSuccesful, targetChunk, 
                                  targetShard >>

DRIVER_CATCHUP == /\ pc[1] = "DRIVER_CATCHUP"
                  /\ IF ~writesBlocked[chunkToMove]
                        THEN /\ pc' = [pc EXCEPT ![1] = "DRIVER_COMPUTE_MODS"]
                        ELSE /\ pc' = [pc EXCEPT ![1] = "DRIVER_LAST_COMPUTE_MODS"]
                  /\ UNCHANGED << allDocs, chunks, pendingWrites, 
                                  writesBlocked, moveInProgress, ownership, 
                                  shardDocs, stack, mods, destShard, i, 
                                  chunkToMove, mods_, sourceShard, destShard_, 
                                  i_, mod, docsToCopy, write, writeSuccesful, 
                                  targetChunk, targetShard >>

DRIVER_COMPUTE_MODS == /\ pc[1] = "DRIVER_COMPUTE_MODS"
                       /\ mods_' = pendingWrites[chunkToMove]
                       /\ pendingWrites' = [pendingWrites EXCEPT ![chunkToMove] = <<>>]
                       /\ pc' = [pc EXCEPT ![1] = "DRIVER_ENTER_CS"]
                       /\ UNCHANGED << allDocs, chunks, writesBlocked, 
                                       moveInProgress, ownership, shardDocs, 
                                       stack, mods, destShard, i, chunkToMove, 
                                       sourceShard, destShard_, i_, mod, 
                                       docsToCopy, write, writeSuccesful, 
                                       targetChunk, targetShard >>

DRIVER_ENTER_CS == /\ pc[1] = "DRIVER_ENTER_CS"
                   /\ IF Len(mods_) < THRESHOLD
                         THEN /\ pc' = [pc EXCEPT ![1] = "DRIVER_BLOCK_WRITES"]
                         ELSE /\ pc' = [pc EXCEPT ![1] = "DRIVER_TRANSFER_MODS"]
                   /\ UNCHANGED << allDocs, chunks, pendingWrites, 
                                   writesBlocked, moveInProgress, ownership, 
                                   shardDocs, stack, mods, destShard, i, 
                                   chunkToMove, mods_, sourceShard, destShard_, 
                                   i_, mod, docsToCopy, write, writeSuccesful, 
                                   targetChunk, targetShard >>

DRIVER_BLOCK_WRITES == /\ pc[1] = "DRIVER_BLOCK_WRITES"
                       /\ writesBlocked' = [writesBlocked EXCEPT ![chunkToMove] = TRUE]
                       /\ pc' = [pc EXCEPT ![1] = "DRIVER_TRANSFER_MODS"]
                       /\ UNCHANGED << allDocs, chunks, pendingWrites, 
                                       moveInProgress, ownership, shardDocs, 
                                       stack, mods, destShard, i, chunkToMove, 
                                       mods_, sourceShard, destShard_, i_, mod, 
                                       docsToCopy, write, writeSuccesful, 
                                       targetChunk, targetShard >>

DRIVER_TRANSFER_MODS == /\ pc[1] = "DRIVER_TRANSFER_MODS"
                        /\ /\ destShard' = [destShard EXCEPT ![1] = destShard_]
                           /\ mods' = [mods EXCEPT ![1] = mods_]
                           /\ stack' = [stack EXCEPT ![1] = << [ procedure |->  "transferMods",
                                                                 pc        |->  "DRIVER_CATCHUP",
                                                                 i         |->  i[1],
                                                                 mods      |->  mods[1],
                                                                 destShard |->  destShard[1] ] >>
                                                             \o stack[1]]
                        /\ i' = [i EXCEPT ![1] = 1]
                        /\ pc' = [pc EXCEPT ![1] = "TRANSFER_MODS"]
                        /\ UNCHANGED << allDocs, chunks, pendingWrites, 
                                        writesBlocked, moveInProgress, 
                                        ownership, shardDocs, chunkToMove, 
                                        mods_, sourceShard, destShard_, i_, 
                                        mod, docsToCopy, write, writeSuccesful, 
                                        targetChunk, targetShard >>

DRIVER_LAST_COMPUTE_MODS == /\ pc[1] = "DRIVER_LAST_COMPUTE_MODS"
                            /\ mods_' = pendingWrites[chunkToMove]
                            /\ pendingWrites' = [pendingWrites EXCEPT ![chunkToMove] = <<>>]
                            /\ pc' = [pc EXCEPT ![1] = "DRIVER_LAST_TRANSFER_MODS"]
                            /\ UNCHANGED << allDocs, chunks, writesBlocked, 
                                            moveInProgress, ownership, 
                                            shardDocs, stack, mods, destShard, 
                                            i, chunkToMove, sourceShard, 
                                            destShard_, i_, mod, docsToCopy, 
                                            write, writeSuccesful, targetChunk, 
                                            targetShard >>

DRIVER_LAST_TRANSFER_MODS == /\ pc[1] = "DRIVER_LAST_TRANSFER_MODS"
                             /\ /\ destShard' = [destShard EXCEPT ![1] = destShard_]
                                /\ mods' = [mods EXCEPT ![1] = mods_]
                                /\ stack' = [stack EXCEPT ![1] = << [ procedure |->  "transferMods",
                                                                      pc        |->  "DRIVER_COMMIT_MOVE",
                                                                      i         |->  i[1],
                                                                      mods      |->  mods[1],
                                                                      destShard |->  destShard[1] ] >>
                                                                  \o stack[1]]
                             /\ i' = [i EXCEPT ![1] = 1]
                             /\ pc' = [pc EXCEPT ![1] = "TRANSFER_MODS"]
                             /\ UNCHANGED << allDocs, chunks, pendingWrites, 
                                             writesBlocked, moveInProgress, 
                                             ownership, shardDocs, chunkToMove, 
                                             mods_, sourceShard, destShard_, 
                                             i_, mod, docsToCopy, write, 
                                             writeSuccesful, targetChunk, 
                                             targetShard >>

DRIVER_COMMIT_MOVE == /\ pc[1] = "DRIVER_COMMIT_MOVE"
                      /\ ownership' = [ownership EXCEPT ![chunkToMove] = destShard_]
                      /\ pc' = [pc EXCEPT ![1] = "DRIVER_UNBLOCK_WRITES"]
                      /\ UNCHANGED << allDocs, chunks, pendingWrites, 
                                      writesBlocked, moveInProgress, shardDocs, 
                                      stack, mods, destShard, i, chunkToMove, 
                                      mods_, sourceShard, destShard_, i_, mod, 
                                      docsToCopy, write, writeSuccesful, 
                                      targetChunk, targetShard >>

DRIVER_UNBLOCK_WRITES == /\ pc[1] = "DRIVER_UNBLOCK_WRITES"
                         /\ writesBlocked' = [writesBlocked EXCEPT ![chunkToMove] = FALSE]
                         /\ pc' = [pc EXCEPT ![1] = "DRIVER_START"]
                         /\ UNCHANGED << allDocs, chunks, pendingWrites, 
                                         moveInProgress, ownership, shardDocs, 
                                         stack, mods, destShard, i, 
                                         chunkToMove, mods_, sourceShard, 
                                         destShard_, i_, mod, docsToCopy, 
                                         write, writeSuccesful, targetChunk, 
                                         targetShard >>

driver == DRIVER_START \/ DRIVER_PICK_CHUNK \/ DRIVER_PICK_SHARD
             \/ DRIVER_START_MOVE \/ DRIVER_CLONING \/ DRIVER_CATCHUP
             \/ DRIVER_COMPUTE_MODS \/ DRIVER_ENTER_CS
             \/ DRIVER_BLOCK_WRITES \/ DRIVER_TRANSFER_MODS
             \/ DRIVER_LAST_COMPUTE_MODS \/ DRIVER_LAST_TRANSFER_MODS
             \/ DRIVER_COMMIT_MOVE \/ DRIVER_UNBLOCK_WRITES

WRITER_START == /\ pc[2] = "WRITER_START"
                /\ writeSuccesful' = FALSE
                /\ \E pickedWrite \in (Docs \X Values):
                     write' = Write(pickedWrite)
                /\ pc' = [pc EXCEPT ![2] = "WRITER_TRY_WRITE"]
                /\ UNCHANGED << allDocs, chunks, pendingWrites, writesBlocked, 
                                moveInProgress, ownership, shardDocs, stack, 
                                mods, destShard, i, chunkToMove, mods_, 
                                sourceShard, destShard_, i_, mod, docsToCopy, 
                                targetChunk, targetShard >>

WRITER_TRY_WRITE == /\ pc[2] = "WRITER_TRY_WRITE"
                    /\ IF ~writeSuccesful
                          THEN /\ targetChunk' = DocToChunk(write.key)
                               /\ targetShard' = ownership[targetChunk']
                               /\ (Len(pendingWrites[targetChunk']) < MAX_WRITES)
                               /\ pc' = [pc EXCEPT ![2] = "WRITER_WRITE"]
                          ELSE /\ pc' = [pc EXCEPT ![2] = "WRITER_START"]
                               /\ UNCHANGED << targetChunk, targetShard >>
                    /\ UNCHANGED << allDocs, chunks, pendingWrites, 
                                    writesBlocked, moveInProgress, ownership, 
                                    shardDocs, stack, mods, destShard, i, 
                                    chunkToMove, mods_, sourceShard, 
                                    destShard_, i_, mod, docsToCopy, write, 
                                    writeSuccesful >>

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
                /\ UNCHANGED << chunks, writesBlocked, moveInProgress, 
                                ownership, stack, mods, destShard, i, 
                                chunkToMove, mods_, sourceShard, destShard_, 
                                i_, mod, docsToCopy, write, targetChunk, 
                                targetShard >>

writer == WRITER_START \/ WRITER_TRY_WRITE \/ WRITER_WRITE

Next == driver \/ writer
           \/ (\E self \in ProcSet: transferMods(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(driver) /\ WF_vars(transferMods(1))
        /\ WF_vars(writer)

\* END TRANSLATION 
=============================================================================
\* Modification History
\* Last modified Thu May 16 16:29:44 CEST 2024 by dgomezferro
\* Created Wed May 15 14:17:17 CEST 2024 by dgomezferro
