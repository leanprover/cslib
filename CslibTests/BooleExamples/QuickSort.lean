/-
QuickSort
-/


-- Strata and Mathlib use different Lean versions, so we can't import Strata currently.
/-
def LinearSearchEnv :=
#strata
program Boogie;

type Array = [int]int;

procedure Swap(a: Array, i: int, j: int) returns (result: Array)
{
    result := a[i := a[j]][j := a[i]];
}

procedure Partition(a: Array, low: int, high: int) returns (result: Array, pivotIndex: int)
  requires low <= high;
  modifies a;
{
    var pivot: int;
    var i: int;
    var j: int;
    var temp: Array;

    pivot := a[high];
    i := low - 1;
    j := low;

    while (j < high)
      invariant low - 1 <= i < j <= high;
    {
        if (a[j] <= pivot) {
            i := i + 1;
            call temp := Swap(a, i, j);
            a := temp;
        }
        j := j + 1;
    }

    call temp := Swap(a, i + 1, high);
    a := temp;
    result := a;
    pivotIndex := i + 1;
}

procedure QuickSort(a: Array, low: int, high: int) returns (result: Array)
  requires low <= high;
  modifies a;
{
    var partitionedArray: Array;
    var pi: int;
    var leftSorted: Array;
    var rightSorted: Array;

    if (low < high) {
        call partitionedArray, pi := Partition(a, low, high);
        call leftSorted := QuickSort(partitionedArray, low, pi - 1);
        call rightSorted := QuickSort(leftSorted, pi + 1, high);
        result := rightSorted;
    } else {
        result := a;
    }
}

procedure SortArray(a: Array, length: int) returns (sorted: Array)
  requires length >= 0;
  modifies a;
{
    if (length <= 1) {
        sorted := a;
    } else {
        call sorted := QuickSort(a, 0, length - 1);
    }
}

#end

-/
