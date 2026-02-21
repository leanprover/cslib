/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import Cslib.Foundations.Data.BiTape
import Cslib.Foundations.Data.RelatesInSteps

public import Cslib.Computability.Machines.MultiTapeTuring.Basic
public import Cslib.Computability.Machines.MultiTapeTuring.ListEncoding
public import Cslib.Computability.Machines.MultiTapeTuring.HeadStats

-- TODO create a "common file"
import Cslib.Computability.Machines.SingleTapeTuring.Basic

namespace Turing


-- This is an attempt at proving Savitch's theorem. We start by stating a generic
-- space-efficient graph reachability algorithm.

/-

General idea, assume distance is power of two:

def reachable(a, b, t, r):
  if t = 0:
    return r(a, b)
  else:
    for c in vertices:
      if reachable(a, c, t - 1, r) and reachable(c, b, t - 1, r):
        return True
    return False

Until we have a generic mechanism for recursion, let's translate this into a program that
uses "goto", and every variable is a stack:

def reachable(a, b, t, r):
  terminate = 0
  result = 0
  section = [0]
  while !terminate:
    match section.pop()
    | 0 =>
      if t = 0:
        result = r(a, b)
        terminate = 1
        section.push(7)
      else:
        section.push(1)
    | 1 =>
      c.push(0)
      section.push(2)
    | 2 =>
      if c.top() = num_vertices:
        section.push(6)
      else:
        a.push(a.top())
        b.push(c.top())
        section.push(0)
        t.push(t.top() - 1)
        section.push(3)
    | 3 =>
      section.push(4)



-/


end Turing
