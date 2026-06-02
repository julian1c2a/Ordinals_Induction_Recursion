mutual
  inductive UCode : Type
    | unit : UCode
    | nat  : UCode
    | sum  : UCode → UCode → UCode
    | pi   : (A : UCode) → (El A → UCode) → UCode
    | univ : Nat → UCode

  inductive El : UCode → Type
    | mk : El .unit
end
