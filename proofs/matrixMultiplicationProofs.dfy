include "../matrixMultiplication.dfy"
include "matrixFunctionProofs.dfy"
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
        vecDotProdDistR (row_i, vec1, vec2);
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

// v1 = v2 => A v1 = A v2
lemma matVecMultEq (mat : Matrix, vec1 : Vector, vec2 : Vector)
requires matNumCols (mat) == vecLength (vec1)
requires vecLength (vec1) == vecLength (vec2)
requires vecEquals (vec1, vec2)
ensures vecEquals (matVecMult (mat, vec1), matVecMult (mat, vec2))
{
    matVecMultAuxEq (mat, vec1, vec2, 0);
}

lemma matVecMultAuxEq (mat : Matrix, vec1 : Vector, vec2 : Vector, i : int)
requires matNumCols (mat) == vecLength (vec1)
requires vecLength (vec1) == vecLength (vec2)
requires vecEquals (vec1, vec2)
requires 0 <= i <= matNumRows (mat)
ensures vecEquals (matVecMultAux (mat, vec1, i), matVecMultAux (mat, vec2, i))
decreases matNumRows (mat) - i
{
    if i < matNumRows (mat) {
        matVecMultAuxEq (mat, vec1, vec2, i + 1);
        vecDotProdEqL (vec1, vec2, matGetRow (mat, i));
        vecDotProdSymm (vec1, matGetRow (mat, i));
        vecDotProdSymm (vec2, matGetRow (mat, i));
        vecEqualsAppend (
            matVecMultAux (mat, vec1, i + 1),
            matVecMultAux (mat, vec2, i + 1),
            vecDotProd (matGetRow (mat, i), vec1)
        );
    }
}

lemma matMatVecMultAssoc (mat1 : Matrix, mat2 : Matrix, vec : Vector)
requires matNumCols (mat1) == matNumRows (mat2)
requires matNumCols (mat2) == vecLength (vec)
ensures vecEquals (matVecMult (mat1, matVecMult (mat2, vec)), matVecMult (matMatMult (mat1, mat2), vec))
{
    matMatVecMultAuxAssoc(mat1, mat2, vec, 0);
}

lemma matMatVecMultAuxAssoc (mat1 : Matrix, mat2 : Matrix, vec : Vector, i : int)
requires matNumCols (mat1) == matNumRows (mat2)
requires matNumCols (mat2) == vecLength (vec)
requires 0 <= i <= matNumRows (mat1)
ensures vecEquals (matVecMultAux (mat1, matVecMult (mat2, vec), i), matVecMultAux (matMatMult (mat1, mat2), vec, i))
decreases matNumRows (mat1) - i
{
    if i == matNumRows (mat1) {
        
    } else {
        matMatVecMultAuxAssoc (mat1, mat2, vec, i + 1);
        matMatVecMultAux2Assoc (mat1, mat2, vec, i, 0);
        assert vecEquals (matVecMult (mat2, vec), matVecMultAux2 (mat2, vec, 0, 0));
        vecDotProdEqR (matGetRow (mat1, i), matVecMult (mat2, vec), matVecMultAux2 (mat2, vec, 0, 0));
        assert vecDotProd (matGetRow (mat1, i), matVecMult (mat2, vec)) == vecDotProd (matGetRow (matMatMult (mat1, mat2), i), vec);
        vecEqualsAppend (
            matVecMultAux (mat1, matVecMult (mat2, vec), i + 1),
            matVecMultAux (matMatMult (mat1, mat2), vec, i + 1),
            vecDotProd (matGetRow (mat1, i), matVecMult (mat2, vec))
        );
    }
}

lemma matMatVecMultAux2Assoc (mat1 : Matrix, mat2 : Matrix, vec : Vector, i : int, j : int)
requires matNumCols (mat1) == matNumRows (mat2)
requires matNumCols (mat2) == vecLength (vec)
requires 0 <= i < matNumRows (mat1)
requires 0 <= j <= matNumCols (mat2)
ensures vecDotProd (matGetRow (mat1, i), matVecMultAux2 (mat2, vec, 0, j)) ==
        vecDotProdAux (matGetRow (matMatMult (mat1, mat2), i), vec, j)
decreases matNumCols (mat2) - j
{
    if j == matNumCols (mat2) {
        assert forall k | 0 <= k < matNumRows (mat2) :: 
            vecGet (matVecMultAux2 (mat2, vec, 0, j), k) == vecDotProdAux (matGetRow (mat2, k), vec, j);
        vecDotProdZero (matGetRow (mat1, i), matVecMultAux2 (mat2, vec, 0, j));
    } else {
        matMatVecMultAux2Assoc (mat1, mat2, vec, i, j + 1);
        matVecMultCol (mat2, vec, j);
        vecDotProdEqR (
            matGetRow (mat1, i),
            matVecMultAux2 (mat2, vec, 0, j),
            vecAdd (vecScale (vecGet (vec, j), matGetCol (mat2, j)), matVecMultAux2 (mat2, vec, 0, j + 1))
        );
        vecDotProdDistR (matGetRow (mat1, i), vecScale (vecGet (vec, j), matGetCol (mat2, j)), matVecMultAux2 (mat2, vec, 0, j + 1));
        vecDotProdScaleR (vecGet (vec, j), matGetRow (mat1, i), matGetCol (mat2, j));
    }
}
