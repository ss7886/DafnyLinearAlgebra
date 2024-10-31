include "../matrixMultiplication.dfy"
include "vectorFunctionProofs.dfy"
include "vectorProofs.dfy"

// A(x + y) = Ax + Ay
lemma matVecMultDist (mat : Matrix, vec1 : Vector, vec2 : Vector)
requires matNumCols (mat) == vecLength (vec1)
requires vecLength (vec1) == vecLength (vec2)
ensures vecEquals (matVecMult (mat, vecAdd (vec1, vec2)), vecAdd (matVecMult (mat, vec1), matVecMult (mat, vec2)))
{
    matVecMultAuxDist (mat, vec1, vec2, 0);
}

lemma matVecMultAuxDist (mat : Matrix, vec1 : Vector, vec2 : Vector, i : int)
requires matNumCols (mat) == vecLength (vec1)
requires vecLength (vec1) == vecLength (vec2)
requires 0 <= i <= matNumRows (mat)
ensures vecEquals (matVecMultAux (mat, vecAdd (vec1, vec2), i), vecAdd (matVecMultAux (mat, vec1, i), matVecMultAux (mat, vec2, i)))
decreases matNumRows (mat) - i
{
    if i < matNumRows (mat) {
        var vec12 := vecAdd (vec1, vec2);
        var row_i := matGetRow (mat, i);
        var add_res := vecAdd (matVecMultAux (mat, vec1, i), matVecMultAux (mat, vec2, i));
        matVecMultAuxDist (mat, vec1, vec2, i + 1);
        vecDotProdDistRH (row_i, vec1, vec2);
        vecEqualsAppend (
            matVecMultAux (mat, vec12, i + 1),
            vecAdd (matVecMultAux (mat, vec1, i + 1), matVecMultAux (mat, vec2, i + 1)),
            vecDotProd (row_i, vec12)
        ); 
        vecAppendDist (
            vecDotProd (row_i, vec1),
            vecDotProd (row_i, vec2),
            matVecMultAux (mat, vec1, i + 1),
            matVecMultAux (mat, vec2, i + 1)
        );
    }
}