include "vectorFunctions.dfy"

function matVecMult (mat : Matrix, vec : Vector) : (res : Vector)
reads *
requires matNumCols (mat) == vecLength (vec)
ensures vecLength (res) == matNumRows (mat)
ensures forall i | 0 <= i < matNumRows (mat) :: vecGet (res, i) == vecDotProd (matGetRow (mat, i), vec)
{
    matVecMultAux (mat, vec, 0)
}

function matVecMultAux (mat : Matrix, vec : Vector, i : int) : (res : Vector)
reads *
requires matNumCols (mat) == vecLength (vec)
requires 0 <= i <= matNumRows (mat)
ensures vecLength (res) == matNumRows (mat) - i
ensures forall j | i <= j < matNumRows (mat) :: vecGet (res, j - i) == vecDotProd (matGetRow (mat, j), vec)
decreases matNumRows (mat) - i
{
    if i == matNumRows (mat) 
    then vecEmpty
    else
        var row := matGetRow (mat, i);
        vecAppend (vecDotProd (row, vec), matVecMultAux (mat, vec, i + 1))
}

lemma matVecMultAuxDist (mat : Matrix, vec1 : Vector, vec2 : Vector, i : int)
requires matNumCols (mat) == vecLength (vec1)
requires vecLength (vec1) == vecLength (vec2)
requires 0 <= i <= matNumRows (mat)
ensures vecEquals (matVecMultAux (mat, vecAdd (vec1, vec2), i), vecAdd (matVecMultAux (mat, vec1, i), matVecMultAux (mat, vec2, i)))
decreases matNumRows (mat) - i
{
    if i == matNumRows (mat) {

    }
    else {
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

// A(x + y) = Ax + Ay
lemma matVecMultDist (mat : Matrix, vec1 : Vector, vec2 : Vector)
requires matNumCols (mat) == vecLength (vec1)
requires vecLength (vec1) == vecLength (vec2)
ensures vecEquals (matVecMult (mat, vecAdd (vec1, vec2)), vecAdd (matVecMult (mat, vec1), matVecMult (mat, vec2)))
{
    matVecMultAuxDist (mat, vec1, vec2, 0);
}