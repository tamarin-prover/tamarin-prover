

type 'a btree =  Empty 
            | Node of 'a * 'a btree * 'a btree 

let rec fold_bottom f zero = function
    | Empty -> zero
    | Node(y, left, right) -> 
            let res_l = fold_bottom f zero left
            and res_r = fold_bottom f zero right
            in
              f res_l res_r y

              (* Not sure if this works, and nothing but an idea of how to fold
               * a tree *)
let rec fold_top f join zero = function
    | Empty -> zero
    | Node(y, left, right) -> 
            let acc = f zero y
            in
            let res_left = fold_top f join acc left
            and res_right = fold_top f join acc right
            in
            join acc res_left res_right


