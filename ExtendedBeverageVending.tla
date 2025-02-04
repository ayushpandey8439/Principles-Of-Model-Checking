---------------------- MODULE ExtendedBeverageVending ----------------------
EXTENDS Naturals, Sequences

CONSTANT maxBeers, maxSodas
VARIABLES state, coin, beers, sodas
vars == <<state, coin, beers, sodas>>
States == { "refill", "pay", "select", "beer", "soda" }



Init == state \in {"pay"} /\ coin=0 /\ beers = maxBeers /\ sodas = maxSodas 

refill == /\ state = "refill"
          /\ beers' = maxBeers
          /\ sodas' = maxSodas
          /\ state' = "select"
          /\ UNCHANGED<<coin>>

PayMoney == /\ state = "pay"
            /\ coin = 0
            /\ coin' = coin + 1
            /\ state' = "select"
            /\ UNCHANGED<<beers,sodas>>

SelectBeverage == /\ state = "select"
                  /\ (\/ (state' = "beer" /\ beers > 0 /\ UNCHANGED<<beers,sodas, coin>>) 
                      \/ (state'= "soda" /\ sodas > 0 /\ UNCHANGED<<beers,sodas, coin>>) 
                      \/ (state' = "refill" /\ (beers = 0 \/ sodas = 0) /\ UNCHANGED<<beers, sodas, coin>>)
                      )

DispenseSoda == /\ state \in {"soda"}
                    /\( (state' = "pay" /\ sodas > 0) \/ (state' = "refill" /\ sodas = 0))
                    /\ sodas' = sodas - 1
                    /\ coin' = coin - 1
                    /\ UNCHANGED <<beers>>
                    
DispenseBeer == /\ state \in {"beer"}
                    /\ ( (state' = "pay" /\ beers > 0) \/ (state'="refill" /\ beers =0))
                    /\ beers' = beers - 1
                    /\ coin' = coin - 1
                    /\ UNCHANGED <<sodas>>

Next == 
    \/ PayMoney
    \/ refill
    \/ SelectBeverage
    \/ DispenseBeer
    \/ DispenseSoda

Spec == Init /\ [][Next]_vars

ExecutionInvariant == /\ state \in {"soda", "beer"} => coin > 0

=============================================================================
\* Modification History
\* Last modified Mon Feb 03 17:13:50 CET 2025 by pandey
\* Created Mon Feb 03 16:28:55 CET 2025 by pandey
