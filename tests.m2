TEST ///
    I = ideal table2(3)    
    assert(fSplittingHeight(I)==3) 
    assert(quasiFSplittingNumber(I,7)==3) 
    ///

TEST ///
    S = (ZZ/5)[x,y]
    I = ideal(x^2-y^3)
    R = S/I
    W2S = witt(2,S)
    W2R = witt(2,R)
    assert(char(W2S.overring) == 25)
    assert(char(W2R.overring) == 25)
///
