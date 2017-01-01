(* $Id: bigint.ml,v 1.5 2014-11-11 15:06:24-08 - - $ *)
(*Amit Khatri 1398993*)
(*Marcos Chabolla 1437530 *)
open Printf

module Bigint = struct

    type sign     = Pos | Neg
    type bigint   = Bigint of sign * int list
    let  radix    = 10
    let  radixlen =  1
    let length    = List.length
    let car       = List.hd
    let cdr       = List.tl
    let map       = List.map
    let reverse   = List.rev
    let strcat    = String.concat
    let strlen    = String.length
    let strsub    = String.sub
    let zero      = Bigint (Pos, [])

    let charlist_of_string str = 
        let last = strlen str - 1
        in  let rec charlist pos result =
            if pos < 0
            then result
            else charlist (pos - 1) (str.[pos] :: result)
        in  charlist last []

    let bigint_of_string str =
        let len = strlen str
        in  let to_intlist first =
                let substr = strsub str first (len - first) in
                let digit char = int_of_char char - int_of_char '0' in
                map digit (reverse (charlist_of_string substr))
            in  if   len = 0
                then zero
                else if   str.[0] = '_'
                     then Bigint (Neg, to_intlist 1)
                     else Bigint (Pos, to_intlist 0)

    let rec string_of_bigint' str count = 
         match str with
        | []              -> "" :: []
        | car::cdr        -> 
                if count = 69 then 
                    "\\\n" :: string_of_bigint' str 0
                else 
                   string_of_int car :: string_of_bigint'
                   cdr (count + 1)
        
    let string_of_bigint (Bigint (sign, value)) =
        match value with
        | []    -> "0"
        | value -> let reversed = reverse value
                      in strcat ""
                      (if sign = Pos 
                        then (string_of_bigint' reversed 0)
                      else "-" :: (string_of_bigint' reversed 1))
                        
                        

    let hello () = Printf.printf "Hello, World!\n";;

    let rec print_list list = match list with
    | [] -> ()
    | car::cdr -> print_int car;
      print_list cdr
      


    let rec add' list1 list2 carry = match (list1, list2, carry) with
        | list1, [], 0       -> list1
        | [], list2, 0       -> list2
        | list1, [], carry   -> add' list1 [carry] 0
        | [], list2, carry   -> add' [carry] list2 0
        | car1::cdr1, car2::cdr2, carry ->
          let sum = car1 + car2 + carry
          in  sum mod radix :: add' cdr1 cdr2 (sum / radix)


    let rec cmp' list1 list2 =
        if list1 = [] 
            then -1
        else if ((car list1) > (car list2))
            then 1
        else if ((car list1) < (car list2))
            then 0
        else cmp' (cdr list1) (cdr list2)    


    let cmp list1 list2 =
        if (length list1) > (length list2)
            then 1
        else if (length list2) > (length list1)
            then 0
        else cmp' (reverse list1) (reverse list2)

    let rec killzeros' list = 
        if (car list) = 0 && length list != 1
            then killzeros' (cdr list)
        else (reverse list)

    let killzeros list = match list with
        | [0] -> list
        | [] -> []
        | list -> killzeros' (reverse list)


    let rec sub' list1 list2 carry = match (list1, list2, carry) with
        | list1, [], 0       -> list1
        | [], list2, 0       -> list2 (*This won't happen*)
        | list1, [], carry   -> sub' list1 [carry] 0
        | [], list2, carry   -> sub' [carry] list2 0 
        | car1::cdr1, car2::cdr2, carry ->
          let diff = car1 - car2 - carry
          in if diff < 0 then
                killzeros( diff + radix :: sub' cdr1 cdr2 1 )
             else 
                 killzeros( diff :: sub' cdr1 cdr2 0 )


    let rec pow' val1 val2 =
        if (car val2) = 1
        then val1
        else (pow' val1 (sub' val2 [1] 0))

    let add (Bigint (neg1, value1)) (Bigint (neg2, value2)) =
        if neg1 = neg2
        then Bigint (neg1, add' value1 value2 0)

        else if neg1 = Pos && neg2 = Neg
        then (
            if (cmp value1 value2 = 1)
            then Bigint (neg1, sub' value1 value2 0)
            else Bigint (neg2, sub' value2 value1 0))

        else if neg1 = Neg && neg2 = Pos
        then (
            if (cmp value1 value2 = 1)
            then Bigint (neg1, sub' value1 value2 0)
            else Bigint (neg2, sub' value2 value1 0))

        else
            if (cmp value1 value2 = 1)
            then Bigint (neg1, sub' value1 value2 0)
            else Bigint (neg2, sub' value2 value1 0)


    let sub (Bigint (neg1, value1)) (Bigint (neg2, value2)) =
        if neg1 = Neg && neg2 = Neg               
        then (
            if (cmp value1 value2 = 1)
            then Bigint (Neg, sub' value1 value2 0)
            else Bigint (Pos, sub' value2 value1 0))

        else if neg1 = Pos && neg2 = Pos
        then (
            if (cmp value1 value2 = 1)
            then Bigint (Pos, sub' value1 value2 0) 
            else Bigint (Neg, sub' value2 value1 0))

        else
            
            Bigint (neg1, add' value1 value2 0)
            
      let double_number number =
          add' number number 0
           
      let rec mul' (value1, pwr2, value2') =
          if(cmp pwr2 value1 = 1)
          then value1, [] (*check this*)
          else let remainder, product = 
                mul'(value1, double_number pwr2, double_number value2')
               in if (cmp remainder pwr2) = 0
                  then remainder, product
                  else (sub' remainder pwr2 0), (add' product value2' 0)
      
      let mul (Bigint (neg1, value1)) (Bigint (neg2,value2)) =
           let _, product = mul'(value1, [1], value2) in
             if neg1 = neg2
             then Bigint(Pos, product)
             else Bigint(Neg, product)
             
    
    let rec divrem' (value1, powerof2, value2) =
        if (cmp value2 value1) = 1
        then [0], value1
        else let quotient, remainder =
            divrem' (value1, double_number powerof2, 
            double_number value2)
             in if (cmp value2 remainder) = 1
                    then quotient, remainder
                else (add' quotient powerof2 0),
                    (sub' remainder value2 0)
    
    
    let divrem ((Bigint (neg1, value1)), (Bigint (neg2, value2))) =
        let quotient, remainder = divrem' (value1, [1], value2)
        in if neg1 = neg2
          then Bigint (Pos, quotient),Bigint (Pos, remainder)
          else Bigint (Neg, quotient),Bigint (Pos, remainder)
     
     let div (Bigint (neg1, value1)) (Bigint (neg2, value2)) =     
        let quotient, _ = 
            divrem ((Bigint (neg1, value1)), (Bigint (neg2, value2)))
             in quotient
      
      let rem (Bigint (neg1, value1)) (Bigint (neg2, value2)) =
        let _, remainder = 
            divrem ((Bigint (neg1, value1)), (Bigint (neg2, value2)))
             in remainder
        
     
    let pow (Bigint (neg1, value1)) (Bigint (neg2, value2)) =
        if neg2 = Neg
            then (Bigint (Pos, [])) (*Makes it zero*)
        else if neg1 = Pos
            then (Bigint (neg1, pow' value1 value2))
        else (Bigint (Pos, pow' value1 value2))

end

