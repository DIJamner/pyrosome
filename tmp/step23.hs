(!! {{e #"blk_subst"
    (#"exch" "G" (ext "H" (#"neg" "B")))
    (#"blk_subst"
        (#"exch" (ext "H" (#"neg" "B")) "G")
        (#"jmp"
            (#"cont"
                (#"prod" "A" (#"neg" "B"))
                (#"pm_pair" (#"hd" (#"prod" "A" (#"neg" "B"))) "e"))
            (#"pair" "v" (#"hd" (#"neg" "B")))))}})