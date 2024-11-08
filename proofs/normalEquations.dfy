include "../matrixMultiplication.dfy"
include "matrixFunctionProofs.dfy"
include "matrixMultiplicationProofs.dfy"
include "vectorFunctionProofs.dfy"

function normalEquations (A : Matrix, b : Vector, ATAinv : Matrix) : (res : Vector)
requires matNumRows (A) == vecLength (b)
requires matNumRows (ATAinv) == matNumCols (ATAinv)
requires matNumCols (A) == matNumRows (ATAinv)
requires matIsInverse (matMatMult (matTr (A), A), ATAinv)
{
    matVecMult (ATAinv, matVecMult (matTr (A), b))
}

// Show ||A(A^T A)^-1 A^T b - b||^2 <= ||Ax - b||^2, when A^T A = (A^T A)^-1 = I
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

    // ||x - A^T b||^2 >= 0.0
    vecNormSqMin (vecSub (x, ATb));
}
