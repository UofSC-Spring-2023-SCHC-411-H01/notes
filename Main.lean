import Notes4.IndPred

open Notes

def main (args : List String) : IO Unit :=
  let l := args.map (fun s => s.toNat!)
  let sorted := insertSort (·≤·) l
  println! "{sorted}"

#eval main ["1","21","10"]
