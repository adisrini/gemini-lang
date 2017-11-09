let
  fun indexof s1 s2 =
    let
      val chars1 = String.explode(s1)
      val chars2 = String.explode(s2)
      fun helper start idx1 idx2 =
        if idx2 = List.length(chars2)
        then start
        else if idx1 = List.length(chars1)
             then ~1
             else if List.nth(chars1, idx1) = List.nth(chars2, idx2)
                  then helper start (idx1+1) (idx2+1)
                  else helper (start+1) (start+1) 0
    in
      helper 0 0 0
    end
in
  indexof "abcdefghijklmnopqrstuvwxyz" "lmno"
end
