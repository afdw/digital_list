
let push t v =
  let n = Array.length t in
  let r = Array.make (n+1) v in
  Array.blit t 0 r 0 n;
  r

let pop t =
  let n = Array.length t in
  let v = t.(n-1) in
  let r = Array.sub t 0 (n-1) in
  v, r

let set t i v =
  let r = Array.copy t in
  r.(i) <- v;
  r
