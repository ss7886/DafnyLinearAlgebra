include "../matrixFunctions.dfy"
include "../matrixMultiplication.dfy"
include "../vectorFunctions.dfy"
include "vectorFunctionProofs.dfy"

lemma matTrRowsCols (mat : Matrix)
ensures forall i | 0 <= i < matNumRows (mat) :: 
    vecEquals (matGetRow (mat, i), matGetCol (matTr (mat), i))
ensures forall i | 0 <= i < matNumCols (mat) :: 
    vecEquals (matGetCol (mat, i), matGetRow (matTr (mat), i))
{}

// <M v1, v2> == <v1, M^T v2>
lemma dotProdTr (mat : Matrix, vec1 : Vector, vec2 : Vector)
requires matNumCols (mat) == vecLength (vec1)
requires matNumRows (mat) == vecLength (vec2)
ensures vecDotProd (matVecMult (mat, vec1), vec2) == vecDotProd (vec1, matVecMult (matTr (mat), vec2))
{
    dotProdTrAux (mat, vec1, vec2, 0);
    matVecMultAuxEquiv (mat, vec1, 0);
}

// Seperate way of defining matrix-vector multiplication, necessary to prove dotProdTr
// Multiplies mat by vec, starting with the jth column of mat and the jth element of vec
function matVecMultAux2 (mat : Matrix, vec : Vector, i : int, j : int) : (res : Vector)
requires matNumCols (mat) == vecLength (vec)
requires 0 <= i <= matNumRows (mat)
requires 0 <= j <= matNumCols (mat)
ensures vecLength (res) == matNumRows (mat) - i
ensures forall k | i <= k < matNumRows (mat) :: vecGet (res, k - i) == vecDotProdAux (matGetRow (mat, k), vec, j)
decreases matNumRows (mat) - i
{
    if i == matNumRows (mat) 
    then vecEmpty
    else
        var row := matGetRow (mat, i);
        vecAppend (vecDotProdAux (row, vec, j), matVecMultAux2 (mat, vec, i + 1, j))
}

lemma matVecMultAuxEquiv (mat : Matrix, vec : Vector, i : int)
requires matNumCols (mat) == vecLength (vec)
requires 0 <= i <= matNumRows (mat)
ensures matVecMultAux (mat, vec, i) == matVecMultAux2 (mat, vec, i, 0)
decreases matNumRows (mat) - i
{}

// Ax = x1 A1 + x2 A2 + ...
// where A1 is the 1st column of A and x1 is the first element of x
lemma matVecMultCol (mat : Matrix, vec : Vector, i : int)
requires matNumCols (mat) == vecLength (vec)
requires 0 <= i < matNumCols (mat)
ensures vecEquals (
    matVecMultAux2 (mat, vec, 0, i),
    vecAdd (vecScale (vecGet (vec, i), matGetCol (mat, i)), matVecMultAux2 (mat, vec, 0, i + 1))
)
{
    assert forall j | 0 <= j < matNumRows (mat) :: 
        vecGet (matVecMultAux2 (mat, vec, 0, i), j) == vecDotProdAux (matGetRow (mat, j), vec, i);
}

lemma dotProdTrAux (mat : Matrix, vec1 : Vector, vec2 : Vector, i : int)
requires matNumCols (mat) == vecLength (vec1)
requires matNumRows (mat) == vecLength (vec2)
requires 0 <= i <= matNumCols (mat)
ensures vecDotProd (matVecMultAux2 (mat, vec1, 0, i), vec2) == 
    vecDotProdAux (vec1, matVecMult (matTr (mat), vec2), i)
decreases matNumCols (mat) - i
{
    if i == matNumCols (mat) {
        assert forall j | 0 <= j < matNumRows (mat) :: 
            vecGet (matVecMultAux2 (mat, vec1, 0, i), j) == 
            vecDotProdAux (matGetRow (mat, j), vec1, i);
        vecDotProdZero (vec2, matVecMultAux2 (mat, vec1, 0, i));
        vecDotProdSymm (vec2, matVecMultAux2 (mat, vec1, 0, i));
    } else {
        dotProdTrAux (mat, vec1, vec2, i + 1);
        matVecMultCol (mat, vec1, i);
        vecDotProdEq (
            matVecMultAux2 (mat, vec1, 0, i), 
            vecAdd (
                vecScale (vecGet (vec1, i), matGetCol (mat, i)),
                matVecMultAux2 (mat, vec1, 0, i + 1)
            ),
            vec2
        );
        vecDotProdDistLH (
            vecScale (vecGet (vec1, i), matGetCol (mat, i)),
            matVecMultAux2 (mat, vec1, 0, i + 1),
            vec2
        );
        vecDotProdScale (vecGet (vec1, i), matGetCol (mat, i), vec2);
        matTrRowsCols (mat);
        vecDotProdEq (matGetRow (matTr (mat), i), matGetCol (mat, i), vec2);
    }
}
