let round_to_int x = int_of_float (floor (x +. 0.5))

let hue2rgb (p, q, t) =
    let t' = if t < 0.0 then t +. 1.0 else if t > 1.0 then t -. 1.0 else t in
    if t' < 1.0 /. 6.0      then p +. (q -. p) *. 6.0 *. t'
    else if t' < 1.0 /. 2.0 then q
    else if t' < 2.0 /. 3.0 then p +. (q -. p) *. (2.0 /. 3.0 -. t') *. 6.0
    else p

let hsl2rgb (h, s, l) =
    let q = if l < 0.5 then l *. (1.0 +. s) else l +. s -. l *. s in
    let p = 2.0 *. l -. q in
    let r = if s = 0.0 then l else hue2rgb (p, q, (h +. 1.0 /. 3.0)) in
    let g = if s = 0.0 then l else hue2rgb (p, q, h) in
    let b = if s = 0.0 then l else hue2rgb (p, q, (h -. 1.0 /. 3.0)) in
  
    (round_to_int (r *. 255.0), round_to_int (g *. 255.0), round_to_int (b *. 255.0))

let rgb2string (r, g, b) = Printf.sprintf "#%02X%02X%02X" r g b

let random_hsl () = (Random.float 1.0, 0.9 +. (Random.float 0.1), 0.5 +. (Random.float 0.1))

let random_rgb_from_hsl () = hsl2rgb (random_hsl ())

let random_rgb () = (Random.int 256, Random.int 256, Random.int 256)
