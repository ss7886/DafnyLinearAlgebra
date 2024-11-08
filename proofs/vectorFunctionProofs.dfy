include "../vectorFunctions.dfy"

// x + y = y + x
lemma vecAddSymmetric (vec1 : Vector, vec2 : Vector)
requires vecLength (vec1) == vecLength (vec2)
ensures vecEquals (vecAdd (vec1, vec2), vecAdd (vec2, vec1))
{}

// (x + y) + z = x + (y + z)
lemma vecAddTransitive (vec1 : Vector, vec2 : Vector, vec3 : Vector)
requires vecLength (vec1) == vecLength (vec2)
requires vecLength (vec1) == vecLength (vec3)
ensures vecEquals (vecAdd (vecAdd (vec1, vec2), vec3), vecAdd (vec1, vecAdd (vec2, vec3)))
{}

lemma vecAddEq (vec1 : Vector, vec2 : Vector, vec3 : Vector)
requires vecLength (vec1) == vecLength (vec2)
requires vecLength (vec2) == vecLength (vec3)
requires vecEquals (vec1, vec2)
ensures vecEquals (vecAdd (vec1, vec3), vecAdd (vec2, vec3))
{}

lemma vecSubEq (vec1 : Vector, vec2 : Vector, vec3 : Vector)
requires vecLength (vec1) == vecLength (vec2)
requires vecLength (vec2) == vecLength (vec3)
requires vecEquals (vec1, vec2)
ensures vecEquals (vecSub (vec1, vec3), vecSub (vec2, vec3))
{}

// <v1, v2> = <v2, v1>
lemma vecDotProdSymm (vec1 : Vector, vec2 : Vector)
requires vecLength (vec1) == vecLength (vec2)
ensures vecDotProd (vec1, vec2) == vecDotProd (vec2, vec1)
{
    vecDotProdAuxSymm (vec1, vec2, 0);
}

lemma vecDotProdAuxSymm (vec1 : Vector, vec2 : Vector, i : int)
requires vecLength (vec1) == vecLength (vec2)
requires 0 <= i <= vecLength (vec1)
ensures vecDotProdAux (vec1, vec2, i) == vecDotProdAux (vec2, vec1, i)
decreases vecLength (vec1) - i
{}

// v1 == v2 => <v1, v3> = <v2, v3>
lemma vecDotProdEqL (vec1 : Vector, vec2 : Vector, vec3 : Vector)
requires vecLength (vec1) == vecLength (vec2)
requires vecLength (vec1) == vecLength (vec3)
requires vecEquals (vec1, vec2)
ensures vecDotProd (vec1, vec3) == vecDotProd (vec2, vec3)
{
    vecDotProdAuxEq (vec1, vec2, vec3, 0);
}

// v2 == v3 => <v1, v2> = <v1, v3>
lemma vecDotProdEqR (vec1 : Vector, vec2 : Vector, vec3 : Vector)
requires vecLength (vec1) == vecLength (vec2)
requires vecLength (vec1) == vecLength (vec3)
requires vecEquals (vec2, vec3)
ensures vecDotProd (vec1, vec2) == vecDotProd (vec1, vec3)
{
    vecDotProdSymm (vec1, vec2);
    vecDotProdSymm (vec1, vec3);
    vecDotProdEqL (vec2, vec3, vec1);
}

lemma vecDotProdAuxEq (vec1 : Vector, vec2 : Vector, vec3 : Vector, i : int)
requires vecLength (vec1) == vecLength (vec2)
requires vecLength (vec1) == vecLength (vec3)
requires vecEquals (vec1, vec2)
requires 0 <= i <= vecLength (vec1)
ensures vecDotProdAux (vec1, vec3, i) == vecDotProdAux (vec2, vec3, i)
decreases vecLength (vec1) - i
{}

lemma vecNormSqEq (vec1 : Vector, vec2 : Vector)
requires vecLength (vec1) == vecLength (vec2)
requires vecEquals (vec1, vec2)
ensures vecNormSq (vec1) == vecNormSq (vec2)
{
    vecDotProdEqL (vec1, vec2, vec1);
    vecDotProdEqR (vec2, vec1, vec2);
}

lemma vecNormSqMin (vec : Vector)
ensures vecNormSq (vec) >= 0.0
{
    vecNormSqMinAux (vec, 0);
}

lemma vecNormSqMinAux (vec : Vector, i : int)
requires 0 <= i <= vecLength (vec)
ensures vecDotProdAux (vec, vec, i) >= 0.0
decreases vecLength (vec) - i
{}

// <a v1, v2> == a <v1, v2>
lemma vecDotProdScaleL (alpha : real, vec1 : Vector, vec2 : Vector)
requires vecLength (vec1) == vecLength (vec2)
ensures vecDotProd (vecScale (alpha, vec1), vec2) == alpha * vecDotProd (vec1, vec2)
{
    vecDotProdAuxScale (alpha, vec1, vec2, 0);
}

// <v1, a v2> == a <v1, v2>
lemma vecDotProdScaleR (alpha : real, vec1 : Vector, vec2 : Vector)
requires vecLength (vec1) == vecLength (vec2)
ensures vecDotProd (vec1, vecScale (alpha, vec2)) == alpha * vecDotProd (vec1, vec2)
{
    vecDotProdSymm (vec1, vecScale(alpha, vec2));
    vecDotProdAuxScale (alpha, vec2, vec1, 0);
    vecDotProdSymm (vec2, vec1);
}

// <a1 v1, a2 v2> == a1 a2 <v1, v2>
lemma vecDotProdScaleRL (alpha1 : real, alpha2 : real, vec1 : Vector, vec2 : Vector)
requires vecLength (vec1) == vecLength (vec2)
ensures vecDotProd (vecScale (alpha1, vec1), vecScale (alpha2, vec2)) == alpha1 * alpha2 * vecDotProd (vec1, vec2)
{
    vecDotProdScaleL (alpha1, vec1, vecScale (alpha2, vec2));
    vecDotProdScaleR (alpha2, vec1, vec2);
}

// ||av||^2 = a^2 ||v||^2
lemma vecNormSqScale (alpha : real, vec : Vector)
ensures vecNormSq (vecScale (alpha, vec)) == alpha * alpha * vecNormSq (vec)
{
    vecDotProdScaleRL (alpha, alpha, vec, vec);
}

lemma vecDotProdAuxScale (alpha : real, vec1 : Vector, vec2 : Vector, i : int)
requires vecLength (vec1) == vecLength (vec2)
requires 0 <= i <= vecLength (vec1)
ensures vecDotProdAux (vecScale (alpha, vec1), vec2, i) == alpha * vecDotProdAux (vec1, vec2, i)
decreases vecLength (vec1) - i
{}

lemma vecDotProdAuxDist (vec1 : Vector, vec2 : Vector, vec3 : Vector, i : int)
requires vecLength (vec1) == vecLength (vec2)
requires vecLength (vec1) == vecLength (vec3)
requires 0 <= i <= vecLength (vec1)
ensures vecDotProdAux (vec1, vecAdd (vec2, vec3), i) == 
    vecDotProdAux (vec1, vec2, i) + vecDotProdAux (vec1, vec3, i)
decreases vecLength (vec1) - i
{}

// <x, y + z> = <x, y> + <x, z>
lemma vecDotProdDistR (vec1 : Vector, vec2 : Vector, vec3 : Vector)
requires vecLength (vec1) == vecLength (vec2)
requires vecLength (vec1) == vecLength (vec3)
ensures vecDotProd (vec1, vecAdd (vec2, vec3)) == vecDotProd (vec1, vec2) + vecDotProd (vec1, vec3)
{
    vecDotProdAuxDist (vec1, vec2, vec3, 0);
}

// <x + y, z> = <x, z> + <y, z>
lemma vecDotProdDistL (vec1 : Vector, vec2 : Vector, vec3 : Vector)
requires vecLength (vec1) == vecLength (vec2)
requires vecLength (vec1) == vecLength (vec3)
ensures vecDotProd (vecAdd (vec1, vec2), vec3) == vecDotProd (vec1, vec3) + vecDotProd (vec2, vec3)
{
    vecDotProdSymm (vecAdd (vec1, vec2), vec3);
    vecDotProdDistR (vec3, vec1, vec2);
    vecDotProdSymm (vec3, vec1);
    vecDotProdSymm (vec3, vec2);
}

// <x + y, w + z> = <x, w> + <x, z> + <y, w> + <y, z>
lemma vecDotProdDistRL (vec1 : Vector, vec2 : Vector, vec3 : Vector, vec4 : Vector)
requires vecLength (vec1) == vecLength (vec2)
requires vecLength (vec1) == vecLength (vec3)
requires vecLength (vec1) == vecLength (vec4)
ensures vecDotProd (vecAdd (vec1, vec2), vecAdd (vec3, vec4)) == 
        vecDotProd (vec1, vec3) + vecDotProd (vec1, vec4) + vecDotProd (vec2, vec3) + vecDotProd (vec2, vec4)
{
    // <v1 + v2, v3 + v4>
    vecDotProdDistR (vecAdd (vec1, vec2), vec3, vec4);
    // <v1 + v2, v3 + v4> = <v1 + v2, v3> + <v1 + v2, v4>
    vecDotProdDistL (vec1, vec2, vec3);
    vecDotProdDistL (vec1, vec2, vec4);
    // <v1 + v2, v3> + <v1 + v2, v4> = <v1, v3> + <v2, v3> + <v1, v4> + <v2, v4>
}

// ||v1 + v2||^2 = ||v1||^2 + 2 <v1, v2> + ||v2||^2
lemma vecNormDist (vec1 : Vector, vec2 : Vector)
requires vecLength (vec1) == vecLength (vec2)
ensures vecNormSq (vecAdd (vec1, vec2)) == vecNormSq (vec1) + 2.0 * vecDotProd (vec1, vec2) + vecNormSq (vec2)
{
    // ||v1 + v2|| = <v1 + v2, v1 + v2>
    vecDotProdDistRL (vec1, vec2, vec1, vec2);
    // <v1 + v2, v1 + v2> = <v1, v1> + <v1, v2> + <v2, v1> + <v2, v2> 
    vecDotProdSymm (vec2, vec1);
    // <v1, v1> + <v1, v2> + <v2, v1> + <v2, v2> = <v1, v1> + 2 <v1, v2> + <v2, v2>
}

// ||v1 - v2||^2 = ||v1||^2 - 2 <v1, v2> + ||v2||^2
lemma vecNormDistSub (vec1 : Vector, vec2 : Vector)
requires vecLength (vec1) == vecLength (vec2)
ensures vecNormSq (vecSub (vec1, vec2)) == vecNormSq (vec1) - 2.0 * vecDotProd (vec1, vec2) + vecNormSq (vec2)
{
    // ||v1 + -v2||^2 == ||v1||^2 + 2 <v1, -v2> + ||-v2||^2
    vecNormDist (vec1, vecScale (-1.0, vec2));
    // <v1, -v2> == - <v1, v2>
    vecDotProdScaleR (-1.0, vec1, vec2);
    // ||-v2||^2 = ||v2||^2
    vecNormSqScale (-1.0, vec2);
}

// (x1 :: vec1) + (x2 :: vec2) == (x1 + x2 :: vec1 + vec2)
lemma vecAppendDist (x1 : real, x2 : real, vec1 : Vector, vec2 : Vector)
requires vecLength (vec1) == vecLength (vec2)
requires vec1.VectorInd? && vec2.VectorInd?
ensures vecEquals (vecAdd (vecAppend (x1, vec1), vecAppend (x2, vec2)), vecAppend (x1 + x2, vecAdd (vec1, vec2)))
{
    var res1 := vecAdd (vecAppend (x1, vec1), vecAppend (x2, vec2));
    var res2 := vecAppend (x1 + x2, vecAdd (vec1, vec2));
    assert forall i | 1 <= i < vecLength (vec1) + 1 ::
            vecGet (res1, i) == 
            vecGet (vec1, i - 1) + vecGet (vec2, i - 1);    
}

lemma vecDotProdZero (vec1 : Vector, vec2 : Vector)
requires vecLength (vec1) == vecLength (vec2)
requires vecZero (vec2)
ensures vecDotProd (vec1, vec2) == 0.0
{
    vecDotProdZeroAux (vec1, vec2, 0);
}

lemma vecDotProdZeroAux (vec1 : Vector, vec2 : Vector, i : int)
requires vecLength (vec1) == vecLength (vec2)
requires vecZero (vec2)
requires 0 <= i <= vecLength (vec1)
ensures vecDotProdAux (vec1, vec2, i) == 0.0
decreases vecLength (vec1) - i
{}
