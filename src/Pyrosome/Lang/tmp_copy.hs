(#"blk_subst"
    (#"exch"
        #"emp"
        "G"
        (ext "H" (#"neg" "B"))
        #"emp")
    (#"blk_subst"
        (#"exch"
            #"emp"
            "H"
            (#"conc" (#"only" (#"neg" "B")) "G")
            #"emp")
        (#"blk_subst"
            (#"exch"
                #"emp"
                (#"only" (#"neg" "B"))
                "G"
                (#"only" "H"))
            (#"pm_pair"
                (#"val_subst"
                    (#"exch"
                        #"emp"
                        (#"only" (#"neg" "B"))
                        "H"
                        #"emp")
                    (#"pair" "v" (#"hd" (#"neg" "B")))))
                "e")))