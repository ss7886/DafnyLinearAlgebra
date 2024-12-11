include "../matrixMultiplication.dfy"
include "matrixFunctionProofs.dfy"
include "matrixMultiplicationProofs.dfy"
include "vectorFunctionProofs.dfy"
include "vectorProofs.dfy"

// ATAinv must be (A^T A)^-1
// Returns (A^T A)^-1 (A^T b)
function normalEquations (A : Matrix, b : Vector, ATAinv : Matrix) : (res : Vector)
requires matNumRows (A) == vecLength (b)
requires matNumRows (ATAinv) == matNumCols (ATAinv)
requires matNumCols (A) == matNumRows (ATAinv)
requires matIsInverse (matMatMult (matTr (A), A), ATAinv)
{
    matVecMult (ATAinv, matVecMult (matTr (A), b))
}

// Show ||A(A^T A)^-1 A^T b - b||^2 <= ||Ax - b||^2, when A^T A = (A^T A)^-1 = I
// In other words, x* = (A^T A)^-1 A^T b is the optimal solution to minimize ||Ax - b||^2
lemma normalEquationsOptATAinv (A : Matrix, b : Vector, ATAinv : Matrix, x : Vector)
requires matNumRows (A) == vecLength (b)
requires matNumCols (A) == vecLength (x)
requires matNumRows (ATAinv) == matNumCols (ATAinv)
requires matNumCols (A) == matNumRows (ATAinv)
requires matIsInverse (matMatMult (matTr (A), A), ATAinv)
requires matIsIdentity (matMatMult (matTr (A), A))
requires matIsIdentity (ATAinv)
ensures vecNormSq (vecSub (matVecMult (A, normalEquations (A, b, ATAinv)), b)) <= 
    vecNormSq (vecSub (matVecMult (A, x), b))
{
    // x* = (A^T A)^-1 A^T b
    var xOpt := normalEquations (A, b, ATAinv);
    var ATb := matVecMult (matTr (A), b);

    // x* = A^T b
    identityVecMult(ATAinv, ATb);
    // A x* = A A^T
    matVecMultEq (A, xOpt, ATb);
    // A x* - b = A A^T - b
    vecSubEq (matVecMult (A, xOpt), matVecMult (A, ATb), b);
    // ||A x* - b|| = ||A A^T b - b||
    vecNormSqEq (vecSub (matVecMult (A, xOpt), b), vecSub (matVecMult (A, ATb), b));
    // ||A A^T b - b||^2 = ||A A^T b||^2 - 2.0 <A A^T b, b> + ||b||^2
    vecNormDistSub (matVecMult (A, ATb), b);
    // ||A A^T b||^2 = <A^T b, A^T A A^T b>
    dotProdTr (A, ATb, matVecMult (A, ATb));
    // A^T (A (A^T b)) = (A^T A) (A^T b)
    matMatVecMultAssoc (matTr (A), A, ATb);
    // (A^T A) (A^T b) = A^T b
    identityVecMult (matMatMult (matTr (A), A), ATb);
    // <A^T b, A^T A A^T b> == <A^T b, A^T b>
    vecDotProdEqR (ATb, matVecMult (matTr (A), matVecMult (A, ATb)), ATb);
    // <A A^T b, b> == <A^T b, A^T b>
    dotProdTr (A, ATb, b);
    // ||A (A^T A)^-1 A^T b - b||^2 = ||b||^2 - ||A^T b||^2
    assert vecNormSq (vecSub (matVecMult (A, xOpt), b)) == vecNormSq (b) - vecNormSq (ATb);

    // ||Ax - b||^2 = ||Ax||^2 - 2.0 <Ax, b> + ||b||^2
    vecNormDistSub (matVecMult (A, x), b);
    // ||Ax||^2 = <x, A^T A x>
    dotProdTr (A, x, matVecMult (A, x));
    // A^T (A x) == (A^T A) x
    matMatVecMultAssoc (matTr (A), A, x);
    // (A^T A) x == x
    identityVecMult (matMatMult (matTr (A), A), x);
    // <x, A^T A x> == <x, x>
    vecDotProdEqR (x, matVecMult (matTr (A), matVecMult (A, x)), x);
    // <Ax, b> == <x, A^T b>
    dotProdTr (A, x, b);
    // ||x - A^T b||^2 == ||x||^2 - 2.0 <x, A^T b> + ||A^T b||^2
    vecNormDistSub (x, ATb);
    // ||Ax - b||^2 = ||x - A^T b||^2 + ||b||^2 - ||A^T b||^2
    assert vecNormSq (vecSub (matVecMult (A, x), b)) == vecNormSq (vecSub (x, ATb)) + vecNormSq (b) - vecNormSq (ATb);

    // ||x - A^T b||^2 >= 0
    vecNormSqMin (vecSub (x, ATb));
}

// Show ||A(A^T A)^-1 A^T b - b||^2 <= ||Ax - b||^2
// In other words, x* = (A^T A)^-1 A^T b is the optimal solution to minimize ||Ax - b||^2
lemma normalEquationsOpt (A : Matrix, b : Vector, ATAinv : Matrix, x : Vector)
requires matNumRows (A) == vecLength (b)
requires matNumCols (A) == vecLength (x)
requires matNumRows (ATAinv) == matNumCols (ATAinv)
requires matNumCols (A) == matNumRows (ATAinv)
requires matIsInverse (matMatMult (matTr (A), A), ATAinv)
requires matIsSymmetric (ATAinv)
ensures vecNormSq (vecSub (matVecMult (A, normalEquations (A, b, ATAinv)), b)) <= 
    vecNormSq (vecSub (matVecMult (A, x), b))
{
    var xOpt := normalEquations (A, b, ATAinv);  // x* := (A^T A)^-1 (A^T b)
    var ATA := matMatMult (matTr (A), A);  // A^T A
    var ATb := matVecMult (matTr (A), b);  // A^T b
    var AxOpt := matVecMult (A, xOpt);  // Ax*
    var Ax := matVecMult (A, x);  // Ax
    var M := matMatMult (ATAinv, ATA);  // M := (A^T A)^-1 (A^T A)
    var Mx := matVecMult (M, x); // Mx

    // Show: ||Ax* - b||^2 <= ||Ax - b||

    // ||Ax* - b||^2 = ||Ax*||^2 - 2 <Ax*, b> + ||b||^2
    vecNormDistSub (AxOpt, b);
    // ||Ax*||^2 = <x*, A^T (Ax*)>
    dotProdTr (A, xOpt, AxOpt);
    // A^T (Ax*) = (A^T A) x*
    matMatVecMultAssoc (matTr (A), A, xOpt);
    // (A^T A) x* = (A^T A) ((A^T A)^-1 (A^T b)) = ((A^T A) (A^T A)^-1) (A^T b)
    matMatVecMultAssoc (matMatMult (matTr (A), A), ATAinv, ATb);
    // (A^T A) (A^T A)^-1 (A^T b) = A^T b
    identityVecMult (matMatMult (ATA, ATAinv), ATb);
    // <x*, A^T (Ax*)> == <x*, A^T b>
    vecDotProdEqR (xOpt, matVecMult (matTr (A), AxOpt), ATb);
    // <x*, A^T b> == <A x*, b>
    dotProdTr (A, xOpt, b);
    // ||Ax* - b||^2 = ||b||^2 - ||Ax*||^2
    assert vecNormSq (vecSub (AxOpt, b)) == vecNormSq (b) - vecNormSq (AxOpt);

    // M x = x
    identityVecMult (M, x);
    // Ax = A (Mx)
    matVecMultEq (A, x, Mx);

    // ||Ax - b||^2 = ||Ax||^2 - 2 <Ax, b> + ||b||^2
    vecNormDistSub (Ax, b);
    // <Ax, b> = <A (Mx), b>
    vecDotProdEqL (Ax, matVecMult (A, Mx), b);
    // <A (Mx), b> = <Mx, A^T b>
    dotProdTr (A, Mx, b);
    // Mx = (A^T A)^-1 ((A^T A) x)
    matMatVecMultAssoc (ATAinv, ATA, x);
    // <Mx, A^T b> = <(A^T A)^-1 ((A^T A) b), A^T b>
    vecDotProdEqL (Mx, matVecMult (ATAinv, matVecMult (ATA, x)), ATb);
    // <(A^T A)^-1 (A^T A) x, A^T b> = <(A^T A) x, ((A^T A)^-1)^T A^T b>
    dotProdTr (ATAinv, matVecMult (ATA, x), ATb);
    // (A^T A)^-1 A^T b = ((A^T A)^-1)^T A^T b
    matEqMultVec (ATAinv, matTr (ATAinv), ATb);
    // <A^T Ax, ((A^T A)^-1)^T A^T b> = <A^T Ax, (A^T A)^-1 A^T b>
    vecDotProdEqR (matVecMult (ATA, x), matVecMult (matTr (ATAinv), ATb), xOpt);
    // (A^T A) x == A^T (A x)
    matMatVecMultAssoc (matTr (A), A, x);
    // <(A^T A) x, x*> == <A^T (A x), x*>
    vecDotProdEqL (matVecMult (ATA, x), matVecMult (matTr (A), Ax), xOpt);
    // <A^T Ax, x*> = <Ax, Ax*>
    dotProdTr (matTr (A), Ax, xOpt);
    // (A^T)^T x*> = Ax*
    matEqMultVec (matTr (matTr (A)), A, xOpt);
    // <Ax, (A^T)^T x*> = <Ax, Ax*>
    vecDotProdEqR (Ax, matVecMult (matTr (matTr (A)), xOpt), AxOpt);
    // <Ax, b> = <Ax, Ax*>
    assert vecDotProd (Ax, b) == vecDotProd (Ax, AxOpt);

    // ||Ax - Ax*|| = ||Ax||^2 - 2 <Ax, Ax*> + ||Ax*||^2
    vecNormDistSub (Ax, AxOpt);
    // ||Ax - b||^2 = ||Ax - Ax*||^2 + ||b||^2 - ||Ax*||^2
    assert vecNormSq (vecSub (Ax, b)) == vecNormSq (vecSub (Ax, AxOpt)) + vecNormSq (b) - vecNormSq (AxOpt);
    // ||Ax - Ax*|| >= 0
    vecNormSqMin (vecSub (Ax, AxOpt));
}
