include "../vector.dfy"

lemma vecEqualsSymm (vec1 : Vector, vec2 : Vector)
requires vecLength (vec1) == vecLength (vec2)
ensures vecEquals (vec1, vec2) <==> vecEquals (vec2, vec1)
{}

lemma vecEqualsTransitive (vec1 : Vector, vec2 : Vector, vec3 : Vector)
requires vecLength (vec1) == vecLength (vec2)
requires vecLength (vec1) == vecLength (vec3)
requires vecEquals (vec1, vec2) && vecEquals (vec2, vec3)
ensures vecEquals (vec1, vec3)
{}

lemma vecEqualsAppend (vec1 : Vector, vec2 : Vector, x : real)
requires vecLength (vec1) == vecLength (vec2)
requires vecEquals (vec1, vec2)
requires vec1.VectorInd? && vec2.VectorInd?
ensures vecEquals (vecAppend (x, vec1), vecAppend (x, vec2))
{
    assert vecGet (vecAppend (x, vec1), 0) == x;
    assert vecGet (vecAppend (x, vec2), 0) == x;
    assert forall i | 1 <= i < vecLength (vec1) + 1 ::
            vecGet (vecAppend (x, vec1), i) == vecGet (vec1, i - 1);
    assert forall i | 1 <= i < vecLength (vec1) + 1 ::
            vecGet (vecAppend (x, vec2), i) == vecGet (vec2, i - 1);
    assert forall i | 1 <= i < vecLength (vec1) + 1 :: 
            vecGet (vecAppend (x, vec1), i) == vecGet (vecAppend (x, vec2), i);
    assert forall i | 0 <= i < vecLength (vec1) + 1 :: vecGet (vecAppend (x, vec1), i) == vecGet (vecAppend (x, vec2), i);
}
