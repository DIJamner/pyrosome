(!! {{e #"blk_subst"
    (#"exch" "G" (ext "H" (#"neg" "B")))
    (#"blk_subst"
        (#"csub"
            (#"id" (ext "H" (#"neg" "B")))
            (#"vsub"
                (#"cont"
                    (#"prod" "A" (#"neg" "B"))
                    (#"pm_pair" (#"hd" (#"prod" "A" (#"neg" "B"))) "e"))))
        (#"blk_subst"
            (#"csub"
                (#"vsub" "v")
                (#"exch" (#"only" (#"neg" "B")) (#"only" (#"neg" (#"prod" "A" (#"neg" "B"))))))
            (#"blk_subst"
                (#"cmp"
                    (#"exch" (#"only" "A") (ext (#"only" (#"neg" (#"prod" "A" (#"neg" "B")))) (#"neg" "B")))
                    (#"csub"
                        (#"id" (#"neg" (#"prod" "A" (#"neg" "B"))))
                        (#"exch" (#"only" (#"neg" "B")) (#"only" "A"))))
                (#"jmp"
                    (#"hd" (#"neg" (#"prod" "A" (#"neg" "B"))))
                    (#"pair" (#"hd" "A") (#"hd" (#"neg" "B")))))))}})