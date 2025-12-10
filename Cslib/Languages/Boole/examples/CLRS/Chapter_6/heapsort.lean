import Strata.Languages.Boogie.Verifier

namespace Strata

-- CLRS Chapter 6: HEAPSORT
-- Pseudo-code adapted from CLRS book (3rd edition), page 160
-- Pseudo-code:
-- HEAPSORT(A)
-- 1  BUILD_MAX_HEAP(A)
-- 2  for i = A.length to 2
-- 3    exchange A[1] with A[i]      
-- 4    A.heapsize = A.heapsize - 1
-- 5    MAX_HEAPIFY(A, 1)
-- To sort an entire array A, the initial call is HEAPSORT(A)

-- BUILD_MAX_HEAP(A)
-- 1 A.heapsize = A.length
-- 2 for i = A.length/2 to 1
-- 3    MAX_HEAPIFY(A, i)

-- MAX_HEAPIFY(A, i)
-- 1 l = LEFT(i)
-- 2 r = RIGHT(i)
-- 3 if l <= A.heapsize and A[l] > A[i]
-- 4    largest = l
-- 5 else largest = i
-- 6 if r <= A.heapsize and A[r] > A[largest]
-- 7    largest = r
-- 8 if largest != i
-- 9    exchange A[i] with A[largest]
-- 10   MAX_HEAPIFY(A, largest)

-- LEFT(i)
-- 1 return 2 * i

-- RIGHT(i)
-- 1 return 2 * i + 1


var A: Map int int;
var heapsize: int;
var n: int; -- array length

private def heapSort :=
#strata
program Boogie;

procedure Left(i: int) return (j: int)
spec
{
    requires i >= 1;
    ensures j >= i;
}
{
    j = 2 * i;
}

procedure Right(i: int) return (j: int)
spec
{
    requires i >= 1;
    ensures j >= i;
}
{
    j = 2 * i + 1;
}

procedure MaxHeapify(i: int) returns ()
spec
{
  requires 1 <= i <= heapsize;
  modifies A;
}
{
    var l: int;
    var r: int;
    var largest: int;
    var tmp: int;
    
    call l := Left(i);
    call r := Right(i);
    
    if (l <= heapsize && A[l] > A[i]) {
        largest := l;
    } else {
        largest := i;
    }

    if (r <= heapsize && A[r] > A[largest]) {
        largest := r;
    }

    if (largest != i) {
        tmp := A[i];
        A := A[i := A[largest]];
        A := A[largest := tmp];

        call MaxHeapify(largest);
    }
  
};

procedure BuildMaxHeap() returns ()
spec
{
  modifies A;
  modifies heapsize;
}
{
    heapsize := n;

    var i: int;
    i := n div 2; -- floor ideally
    while (i >= 1) 
        invariant 1 <= i <= n/2 + 1;
        invariant heapsize == n;
        invariant forall j: int, i + 1 <= j && j <= n ==> A[j/2] >= A[j]; -- IsMaxHeap(i+1, n)
    {
       call MaxHeapify(i);
       i := i - 1; 
    }
};

procedure HeapSort() returns ()
spec
{
    requires n >= 1;
    modifies A;
    modifies heapsize;
}
{
    call BuildMaxHeap();
    var i: int;

    i := n;
    while (i > 1) 
        invariant 1 <= i <= n;
        invariant heapsize == i;
        invariant forall j : int, 2 <= j && j <= i ==> A[j/2] >= A[j];
        invariant forall j, k: int, i + 1 <= j < k <= n => A[j] <= A[k];
    {
        -- swap A[1] and A[i]
        var tmp: int;
        tmp := A[1];
        A := A[1 := A[i]];
        A := A[i := tmp];
        
        heapsize := heapsize - 1
        call MaxHeapify(1);
        i := i - 1; 
    }
};

#end

#eval verify "cvc5" heapSort