sort : Type
nat : Type

term(tRel) : Type

tSort : sort -> term

tProd : term -> (bind term in term) -> term
tLambda : term -> (bind term in term) -> term
tApp : term -> term -> term

tNat : term
tZero : term
tSucc : term -> term
tNatElim : (bind term in term) -> term -> term -> term -> term

tBool : term
tTrue : term
tFalse : term
tBoolElim : (bind term in term) -> term -> term -> term -> term

tAlpha : nat -> term

tEmpty : term
tEmptyElim : (bind term in term) -> term -> term

tTree : term
tLeaf : term -> term
tNode : term -> term -> term -> term
tTreeElim : (bind term in term) -> term -> term -> term -> term 

tSig : term -> (bind term in term) -> term
tPair : term -> (bind term in term) -> term -> term -> term
tFst : term -> term
tSnd : term -> term

tId : term -> term -> term -> term
tRefl : term -> term -> term
tIdElim : term -> term -> (bind term , term in term) -> term -> term -> term -> term

