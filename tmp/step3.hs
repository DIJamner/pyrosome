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
            (#"cmp"
                (#"exch" "H" (ext (#"only" (#"neg" "B")) (#"neg" (#"prod" "A" (#"neg" "B")))))
                (#"csub"
                    (#"vsub"
                        (#"cont"
                            "A"
                            (#"blk_subst"
                                (#"csub"
                                    (#"exch" (#"only" (#"neg" "B")) (#"only" (#"neg" (#"prod" "A" (#"neg" "B")))))
                                    (#"id" (#"only" "A")))
                                (#"jmp"
                                    (#"hd" (#"neg" (#"prod" "A" (#"neg" "B"))))
                                    (#"val_subst"
                                        (#"exch" (#"only" (#"neg" "B")) (#"only" "A"))
                                        (#"pair" (#"hd" "A") (#"hd" (#"neg" "B"))))))))
                    (#"id" "H")))
            (#"jmp" (#"hd" (#"neg" "A")) "v")))}})