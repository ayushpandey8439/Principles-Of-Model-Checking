---------- MODULE BeverageVending ----------
EXTENDS Naturals, Sequences

VARIABLES state, coin
vars == <<state, coin>>
States == { "pay", "select", "beer", "soda" }



Init == state = "pay" /\ coin = 0

PayMoney == /\ state = "pay"
            /\ coin' = coin + 1
            /\ state' = "select"

SelectBeverage == /\ state = "select"
                  /\ coin' = coin - 1
                  /\ \/ state' = "beer" \/ state'= "soda"


DispenseBeverage == /\ state \in {"beer", "soda"}
                    /\ state' = "pay"
                    /\ UNCHANGED <<coin>>

Next == 
    \/ PayMoney
    \/ SelectBeverage
    \/ DispenseBeverage

Spec == Init /\ [][Next]_vars

ExecutionInvariant == /\ state \in {"soda", "beer"} => coin > 0

============================================