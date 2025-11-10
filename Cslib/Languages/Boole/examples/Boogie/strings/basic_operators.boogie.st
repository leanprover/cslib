program Boogie;

function concat(x: string, y: string): string;
function len(x: string): int;
function substr(x: string, y: int, z: int): string;
function indexOf(x: string, y: string): int;
function indexOfFromOffset(x: string, y: string, z: int): int;
function at(x: string, y: int): string;
function contains(x: string, y: string): bool;
function prefixOf(x: string, y: string): bool;
function suffixOf(x: string, y: string): bool;
function replace(x: string, y: string, z: string): string;
function stringToInt(x: string): int;
function intToString(x: int): string;

// axioms for basic string behavior

// length of concatenation = sum of lengths
axiom (forall x: string, y: string :: len(concat(x, y)) == len(x) + len(y));

// each character (returned by at) has length 1
axiom (forall x: string, i: int ::
    0 <= i && i < len(x) ==> len(at(x, i)) == 1);

// every string has non-negative length
axiom (forall x: string :: len(x) >= 0);

// prefix and suffix relationships
axiom (forall x: string, y: string ::
    prefixOf(x, concat(x, y)));       // x is prefix of x+y
axiom (forall x: string, y: string ::
    suffixOf(y, concat(x, y)));       // y is suffix of x+y

// contains relationships
axiom (forall x: string, y: string ::
    contains(concat(x, y), x));       // x+y contains x
axiom (forall x: string, y: string ::
    contains(concat(x, y), y));       // x+y contains y

// index of a prefix is 0
axiom (forall x: string, y: string ::
    indexOf(concat(x, y), x) == 0);
axiom (forall x: string, y: string ::
    indexOfFromOffset(concat(x, y), x, 0) == 0);

// substring extraction behaves as expected
axiom (forall x: string, y: string ::
    substr(concat(x, y), 0, len(x)) == x);
axiom (forall x: string, y: string ::
    substr(concat(x, y), len(x), len(y)) == y);

// replacement axiom: replacing prefix x with y in x+y yields y+y
axiom (forall x: string, y: string ::
    replace(concat(x, y), x, y) == concat(y, y));

// integer/string conversion inverses
axiom (forall i: int :: stringToInt(intToString(i)) == i);
axiom (forall x: string :: intToString(stringToInt(x)) == x);

// characters come from x when i < len(x)
axiom (forall x: string, y: string, i: int ::
    0 <= i && i < len(x) ==> at(concat(x, y), i) == at(x, i));

// characters come from y when i >= len(x)
axiom (forall x: string, y: string, i: int ::
    len(x) <= i && i < len(x) + len(y) ==>
        at(concat(x, y), i) == at(y, i - len(x)));


procedure main() returns () {
    var s1: string, s2: string, s3: string;

    assume len(s1) == 3;
    assume len(s3) == 3;
    assume concat(s1,s2) == s3;

    assert len(s1) + len(s2) == len(s3);

    assert substr(s3, len(s1), len(s2)) == s2;

    assert indexOf(s3, s1) == 0;

    assert indexOfFromOffset(s3, s1, 0) == 0;

    assert at(s3, 2) == at(s1, 2);

    assert contains(s3, s1);

    assert prefixOf(s1, s3);

    assert suffixOf(s2, s3);

    assert replace(s3, s1, s2) == concat(s2, s2);

    // TODO: This used to verify with Z3 4.8.4
    // assert intToString(stringToInt(s1)) == s1;
};