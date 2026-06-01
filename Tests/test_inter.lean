import OrdinalsInductionRecursion.ExtPreOrd

namespace PreOrd

def inter_succ_y (ih_x : PreOrd → PreOrd) : PreOrd → PreOrd
  | .zero => .zero
  | .succ y' => .succ (ih_x y')
  | .sup g => .sup (fun n => inter_succ_y ih_x (g n))

def inter_nested (x : PreOrd) : PreOrd → PreOrd :=
  match x with
  | .zero => fun _ => .zero
  | .sup f => fun y => .sup (fun n => inter_nested (f n) y)
  | .succ x' => inter_succ_y (inter_nested x')

end PreOrd
