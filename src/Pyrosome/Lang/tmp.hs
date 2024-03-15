(#"blk_subst"
    (#"exch"
        #"emp"
        "G"
        (ext "H" (#"neg" "B"))
        #"emp")
    (#"jmp"
        (#"val_subst"
            (#"vsub"
                (#"cont"
                    (#"neg" (#"prod" "A" (#"neg" "B")))
                    (#"blk_subst"
                        (#"cmp"
                            (#"csub"
                                (#"id" "H")
                                (#"vsub"
                                    (#"cont" "A"
                                        (#"blk_subst"
                                            (#"exch"
                                                #"emp"
                                                (#"only" (#"neg" "B"))
                                                (#"only" (#"neg" (#"prod" "A" (#"neg" "B"))))
                                                (#"only" "A"))
                                            (#"jmp"
                                                (#"hd" (#"neg" (#"prod" "A" (#"neg" "B"))))
                                                (#"val_subst"
                                                    (#"exch"
                                                        #"emp"
                                                        (#"only" (#"neg" "B"))
                                                        (#"only" "A")
                                                        #"emp")
                                                    (#"pair"
                                                        (#"hd" "A")
                                                        (#"hd" (#"neg" "B")))))))))
                            (#"exch"
                                #"emp"
                                "H"
                                (#"only" (#"neg" "A"))
                                #"emp"))
                        (#"jmp" (#"hd" (#"neg" "A")) "v"))))
            (#"hd" (#"neg" (#"neg" (#"prod" "A" (#"neg" "B"))))))
        (#"cont"
            (#"prod" "A" (#"neg" "B"))
            (#"pm_pair" (#"hd" (#"prod" "A" (#"neg" "B"))) "e"))))