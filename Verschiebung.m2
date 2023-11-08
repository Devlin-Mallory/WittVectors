
verschiebung=method()
verschiebung(List):=L->(
if length unique apply(L,i->ring i) > 1 then return "error: all elements of tuple must live in the same ring";
{0}|for i from 0 to length L -1  list L_i
)



