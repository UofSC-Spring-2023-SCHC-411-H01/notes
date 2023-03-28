import Notes4.IndPred

open Notes IO

def main (args : List String) : IO Unit := do
  let nums := args.map (fun s => s.toInt!)
  let sorted := insertSort (·≤·) nums
  println s!"{sorted}"
