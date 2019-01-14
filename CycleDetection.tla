--------------------------- MODULE CycleDetection ---------------------------

EXTENDS Naturals

CONSTANTS N

ASSUME N \in Nat

Nodes == 1..N

NIL == CHOOSE NIL : NIL \notin Nodes

(*
--fair algorithm TortoiseAndHare

variables
    start \in Nodes,
    succ \in [Nodes -> Nodes \union {NIL}],
    cycle, tortoise, hare, done;
begin
h0: tortoise := start;
    hare := start;
    done := FALSE;
h1: while ~done do
        h2: tortoise := succ[tortoise];
            hare := LET hare1 == succ[hare] IN
                    IF hare1 \in DOMAIN succ THEN succ[hare1] ELSE NIL;
        h3: if tortoise = NIL \/ hare = NIL then
                cycle := FALSE;
                done := TRUE;
            elsif tortoise = hare then
                cycle := TRUE;
                done := TRUE;
            end if;
    end while;

end algorithm
*)
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES start, succ, cycle, tortoise, hare, done, pc

vars == << start, succ, cycle, tortoise, hare, done, pc >>

Init == (* Global variables *)
        /\ start \in Nodes
        /\ succ \in [Nodes -> Nodes \union {NIL}]
        /\ cycle = defaultInitValue
        /\ tortoise = defaultInitValue
        /\ hare = defaultInitValue
        /\ done = defaultInitValue
        /\ pc = "h0"

h0 == /\ pc = "h0"
      /\ tortoise' = start
      /\ hare' = start
      /\ done' = FALSE
      /\ pc' = "h1"
      /\ UNCHANGED << start, succ, cycle >>

h1 == /\ pc = "h1"
      /\ IF ~done
            THEN /\ pc' = "h2"
            ELSE /\ pc' = "Done"
      /\ UNCHANGED << start, succ, cycle, tortoise, hare, done >>

h2 == /\ pc = "h2"
      /\ tortoise' = succ[tortoise]
      /\ hare' = (LET hare1 == succ[hare] IN
                  IF hare1 \in DOMAIN succ THEN succ[hare1] ELSE NIL)
      /\ pc' = "h3"
      /\ UNCHANGED << start, succ, cycle, done >>

h3 == /\ pc = "h3"
      /\ IF tortoise = NIL \/ hare = NIL
            THEN /\ cycle' = FALSE
                 /\ done' = TRUE
            ELSE /\ IF tortoise = hare
                       THEN /\ cycle' = TRUE
                            /\ done' = TRUE
                       ELSE /\ TRUE
                            /\ UNCHANGED << cycle, done >>
      /\ pc' = "h1"
      /\ UNCHANGED << start, succ, tortoise, hare >>

Next == h0 \/ h1 \/ h2 \/ h3
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION

\* Transitive closure
\* From https://github.com/tlaplus/Examples/blob/master/specifications/TransitiveClosure/TransitiveClosure.tla
TC(R) ==
  LET Support(X) == {r[1] : r \in X} \cup {r[2] : r \in X}
      S == Support(R)
      RECURSIVE TCR(_)
      TCR(T) == IF T = {} 
                  THEN R
                  ELSE LET r == CHOOSE s \in T : TRUE
                           RR == TCR(T \ {r})
                       IN  RR \cup {<<s, t>> \in S \X S : 
                                      <<s, r>> \in RR /\ <<r, t>> \in RR}
  IN  TCR(S)

HasCycle(node) == LET R == {<<s, t>> \in Nodes \X (Nodes \union {NIL}): succ[s] = t }
                  IN <<node, NIL>> \notin TC(R)


\* An alternate definition of HasCycle

HasCycle2(node) ==
  LET R == {<<s, t>> \in Nodes \X (Nodes \union {NIL}): succ[s] = t }
  IN \E n \in Nodes : /\ <<node, n>> \in TC(R) 
                      /\ <<n, n>> \in TC(R)
                  
PartialCorrectness == pc="Done" => (cycle <=> HasCycle(start))


=============================================================================
\* Modification History
\* Last modified Sun Dec 23 10:51:33 PST 2018 by lhochstein
\* Created Sun Oct 15 17:34:00 PDT 2017 by lhochstein
