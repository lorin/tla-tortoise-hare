--------------------------- MODULE CycleDetection ---------------------------

EXTENDS Naturals

CONSTANTS N, NIL, UNKNOWN

Nodes == 1..N


(*
--fair algorithm TortoiseAndHare

variables
    start \in Nodes,
    succ \in [Nodes -> Nodes \union {NIL}],
    tortoise = start,
    hare = start,
    cycle = UNKNOWN,
    done = FALSE;

begin
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
VARIABLES start, succ, tortoise, hare, cycle, done, pc

vars == << start, succ, tortoise, hare, cycle, done, pc >>

Init == (* Global variables *)
        /\ start \in Nodes
        /\ succ \in [Nodes -> Nodes \union {NIL}]
        /\ tortoise = start
        /\ hare = start
        /\ cycle = UNKNOWN
        /\ done = FALSE
        /\ pc = "h1"

h1 == /\ pc = "h1"
      /\ IF ~done
            THEN /\ pc' = "h2"
            ELSE /\ pc' = "Done"
      /\ UNCHANGED << start, succ, tortoise, hare, cycle, done >>

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

Next == h1 \/ h2 \/ h3
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION


=============================================================================
\* Modification History
\* Last modified Sun Oct 15 17:44:09 PDT 2017 by lhochstein
\* Created Sun Oct 15 17:34:00 PDT 2017 by lhochstein
