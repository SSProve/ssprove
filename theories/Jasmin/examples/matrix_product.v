Require Import List.
From Jasmin Require Import expr.
From Jasmin Require Import x86_extra.

Import ListNotations.
Local Open Scope string.

Definition matrix_product :=  {| p_funcs :=
    [(xH,
      {| f_info := xO xH;
       f_tyin :=
        [sword U64;
         sword U64;
         sword U64];
       f_params :=
        [{| v_var :=
           {| vtype := sword U64;
            vname := "x.218" |};
          v_info := dummy_var_info |};
         {| v_var :=
           {| vtype := sword U64;
            vname := "y.219" |};
          v_info := dummy_var_info |};
         {| v_var :=
           {| vtype := sword U64;
            vname := "z.220" |};
          v_info := dummy_var_info |}];
       f_body :=
        [MkI
          (dummy_instr_info)
          (Cfor
           ({| v_var :=
              {| vtype := sint; vname := "i.221" |};
             v_info := dummy_var_info |})
           (((UpTo, Pconst Z0),
            Papp2 (Omul Op_int)
             (Pconst
              (Zpos
                (xO
                  (xI
                    (xO xH)))))
             (Pconst
              (Zpos
                (xO
                  (xI
                    (xO xH)))))))
           ([MkI
             (dummy_instr_info)
             (Cassgn
              (Lvar
                {| v_var :=
                  {| vtype :=
                    sword U64;
                   vname := "tmp.222" |};
                 v_info := dummy_var_info |})
              (AT_none) (sword U64)
              (Pload (U64)
               ({| v_var :=
                 {| vtype :=
                   sword U64;
                  vname := "x.218" |};
                v_info := dummy_var_info |})
               (Papp1 (Oword_of_int U64)
                (Papp2 (Omul Op_int)
                 (Pconst
                  (Zpos
                    (xO
                      (xO
                        (xO xH)))))
                 (Pvar
                  {| gv :=
                    {| v_var :=
                      {| vtype := sint;
                       vname := "i.221" |};
                     v_info := dummy_var_info |};
                   gs := Slocal |})))));
            MkI
             (dummy_instr_info)
             (Cassgn
              (Laset (AAscale) (U64)
                ({| v_var :=
                  {| vtype :=
                    sarr
                     (xO
                       (xO
                         (xO
                           (xO
                             (xO
                               (xI
                                 (xO
                                   (xO
                                     (xI
                                       xH)))))))));
                   vname := "mx.223" |};
                 v_info := dummy_var_info |})
                (Pvar
                 {| gv :=
                   {| v_var :=
                     {| vtype := sint;
                      vname := "i.221" |};
                    v_info := dummy_var_info |};
                  gs := Slocal |}))
              (AT_none) (sword U64)
              (Pvar
               {| gv :=
                 {| v_var :=
                   {| vtype :=
                     sword U64;
                    vname := "tmp.222" |};
                  v_info := dummy_var_info |};
                gs := Slocal |}));
            MkI
             (dummy_instr_info)
             (Cassgn
              (Lvar
                {| v_var :=
                  {| vtype :=
                    sword U64;
                   vname := "tmp.222" |};
                 v_info := dummy_var_info |})
              (AT_none) (sword U64)
              (Pload (U64)
               ({| v_var :=
                 {| vtype :=
                   sword U64;
                  vname := "y.219" |};
                v_info := dummy_var_info |})
               (Papp1 (Oword_of_int U64)
                (Papp2 (Omul Op_int)
                 (Pconst
                  (Zpos
                    (xO
                      (xO
                        (xO xH)))))
                 (Pvar
                  {| gv :=
                    {| v_var :=
                      {| vtype := sint;
                       vname := "i.221" |};
                     v_info := dummy_var_info |};
                   gs := Slocal |})))));
            MkI
             (dummy_instr_info)
             (Cassgn
              (Laset (AAscale) (U64)
                ({| v_var :=
                  {| vtype :=
                    sarr
                     (xO
                       (xO
                         (xO
                           (xO
                             (xO
                               (xI
                                 (xO
                                   (xO
                                     (xI
                                       xH)))))))));
                   vname := "my.224" |};
                 v_info := dummy_var_info |})
                (Pvar
                 {| gv :=
                   {| v_var :=
                     {| vtype := sint;
                      vname := "i.221" |};
                    v_info := dummy_var_info |};
                  gs := Slocal |}))
              (AT_none) (sword U64)
              (Pvar
               {| gv :=
                 {| v_var :=
                   {| vtype :=
                     sword U64;
                    vname := "tmp.222" |};
                  v_info := dummy_var_info |};
                gs := Slocal |}))]));
         MkI
          (dummy_instr_info)
          (Ccall (DoNotInline)
           ([Lvar
             {| v_var :=
               {| vtype :=
                 sarr
                  (xO
                    (xO
                      (xO
                        (xO
                          (xO
                            (xI
                              (xO
                                (xO
                                  (xI
                                    xH)))))))));
                vname := "mz.225" |};
              v_info := dummy_var_info |}])
           (xI xH)
           ([Pvar
             {| gv :=
               {| v_var :=
                 {| vtype :=
                   sarr
                    (xO
                      (xO
                        (xO
                          (xO
                            (xO
                              (xI
                                (xO
                                  (xO
                                    (xI
                                      xH)))))))));
                  vname := "mx.223" |};
                v_info := dummy_var_info |};
              gs := Slocal |};
            Pvar
             {| gv :=
               {| v_var :=
                 {| vtype :=
                   sarr
                    (xO
                      (xO
                        (xO
                          (xO
                            (xO
                              (xI
                                (xO
                                  (xO
                                    (xI
                                      xH)))))))));
                  vname := "my.224" |};
                v_info := dummy_var_info |};
              gs := Slocal |};
            Pvar
             {| gv :=
               {| v_var :=
                 {| vtype :=
                   sarr
                    (xO
                      (xO
                        (xO
                          (xO
                            (xO
                              (xI
                                (xO
                                  (xO
                                    (xI
                                      xH)))))))));
                  vname := "mz.225" |};
                v_info := dummy_var_info |};
              gs := Slocal |}]));
         MkI
          (dummy_instr_info)
          (Cfor
           ({| v_var :=
              {| vtype := sint; vname := "i.221" |};
             v_info := dummy_var_info |})
           (((UpTo, Pconst Z0),
            Papp2 (Omul Op_int)
             (Pconst
              (Zpos
                (xO
                  (xI
                    (xO xH)))))
             (Pconst
              (Zpos
                (xO
                  (xI
                    (xO xH)))))))
           ([MkI
             (dummy_instr_info)
             (Cassgn
              (Lvar
                {| v_var :=
                  {| vtype :=
                    sword U64;
                   vname := "tmp.222" |};
                 v_info := dummy_var_info |})
              (AT_none) (sword U64)
              (Pget (AAscale) (U64)
               ({| gv :=
                 {| v_var :=
                   {| vtype :=
                     sarr
                      (xO
                        (xO
                          (xO
                            (xO
                              (xO
                                (xI
                                  (xO
                                    (xO
                                      (xI
                                        xH)))))))));
                    vname := "mz.225" |};
                  v_info := dummy_var_info |};
                gs := Slocal |})
               (Pvar
                {| gv :=
                  {| v_var :=
                    {| vtype := sint;
                     vname := "i.221" |};
                   v_info := dummy_var_info |};
                 gs := Slocal |})));
            MkI
             (dummy_instr_info)
             (Cassgn
              (Lmem (U64)
                ({| v_var :=
                  {| vtype :=
                    sword U64;
                   vname := "z.220" |};
                 v_info := dummy_var_info |})
                (Papp1 (Oword_of_int U64)
                 (Papp2 (Omul Op_int)
                  (Pconst
                   (Zpos
                     (xO
                       (xO
                         (xO xH)))))
                  (Pvar
                   {| gv :=
                     {| v_var :=
                       {| vtype := sint;
                        vname := "i.221" |};
                      v_info := dummy_var_info |};
                    gs := Slocal |}))))
              (AT_none) (sword U64)
              (Pvar
               {| gv :=
                 {| v_var :=
                   {| vtype :=
                     sword U64;
                    vname := "tmp.222" |};
                  v_info := dummy_var_info |};
                gs := Slocal |}))]))];
       f_tyout := []; f_res := []; f_extra := tt |});
     (xI xH,
      {| f_info :=
        xO (xO xH);
       f_tyin :=
        [sarr
          (xO
            (xO
              (xO
                (xO
                  (xO
                    (xI
                      (xO
                        (xO
                          (xI xH)))))))));
         sarr
          (xO
            (xO
              (xO
                (xO
                  (xO
                    (xI
                      (xO
                        (xO
                          (xI xH)))))))));
         sarr
          (xO
            (xO
              (xO
                (xO
                  (xO
                    (xI
                      (xO
                        (xO
                          (xI xH)))))))))];
       f_params :=
        [{| v_var :=
           {| vtype :=
             sarr
              (xO
                (xO
                  (xO
                    (xO
                      (xO
                        (xI
                          (xO
                            (xO
                              (xI xH)))))))));
            vname := "m1.226" |};
          v_info := dummy_var_info |};
         {| v_var :=
           {| vtype :=
             sarr
              (xO
                (xO
                  (xO
                    (xO
                      (xO
                        (xI
                          (xO
                            (xO
                              (xI xH)))))))));
            vname := "m2.227" |};
          v_info := dummy_var_info |};
         {| v_var :=
           {| vtype :=
             sarr
              (xO
                (xO
                  (xO
                    (xO
                      (xO
                        (xI
                          (xO
                            (xO
                              (xI xH)))))))));
            vname := "res.228" |};
          v_info := dummy_var_info |}];
       f_body :=
        [MkI
          (dummy_instr_info)
          (Cassgn
           (Lvar
             {| v_var :=
               {| vtype :=
                 sarr
                  (xO
                    (xO
                      (xO
                        (xO
                          (xO
                            (xI
                              (xO
                                (xO
                                  (xI
                                    xH)))))))));
                vname := "pres.229" |};
              v_info := dummy_var_info |})
           (AT_none)
           (sarr
            (xO
              (xO
                (xO
                  (xO
                    (xO
                      (xI
                        (xO
                          (xO
                            (xI xH))))))))))
           (Pvar
            {| gv :=
              {| v_var :=
                {| vtype :=
                  sarr
                   (xO
                     (xO
                       (xO
                         (xO
                           (xO
                             (xI
                               (xO
                                 (xO
                                   (xI
                                     xH)))))))));
                 vname := "res.228" |};
               v_info := dummy_var_info |};
             gs := Slocal |}));
         MkI
          (dummy_instr_info)
          (Ccall (DoNotInline)
           ([Lvar
             {| v_var :=
               {| vtype :=
                 sarr
                  (xO
                    (xO
                      (xO
                        (xO
                          (xO
                            (xI
                              (xO
                                (xO
                                  (xI
                                    xH)))))))));
                vname := "m2t.230" |};
              v_info := dummy_var_info |}])
           (xI
            (xO xH))
           ([Pvar
             {| gv :=
               {| v_var :=
                 {| vtype :=
                   sarr
                    (xO
                      (xO
                        (xO
                          (xO
                            (xO
                              (xI
                                (xO
                                  (xO
                                    (xI
                                      xH)))))))));
                  vname := "m2.227" |};
                v_info := dummy_var_info |};
              gs := Slocal |};
            Pvar
             {| gv :=
               {| v_var :=
                 {| vtype :=
                   sarr
                    (xO
                      (xO
                        (xO
                          (xO
                            (xO
                              (xI
                                (xO
                                  (xO
                                    (xI
                                      xH)))))))));
                  vname := "m2t.230" |};
                v_info := dummy_var_info |};
              gs := Slocal |}]));
         MkI
          (dummy_instr_info)
          (Cfor
           ({| v_var :=
              {| vtype := sint; vname := "i.231" |};
             v_info := dummy_var_info |})
           (((UpTo, Pconst Z0),
            Pconst
             (Zpos
               (xO
                 (xI
                   (xO xH))))))
           ([MkI
             (dummy_instr_info)
             (Ccall (DoNotInline)
              ([Lasub (AAscale) (U64)
                (xO
                 (xI
                   (xO xH)))
                ({| v_var :=
                  {| vtype :=
                    sarr
                     (xO
                       (xO
                         (xO
                           (xO
                             (xO
                               (xI
                                 (xO
                                   (xO
                                     (xI
                                       xH)))))))));
                   vname := "rest.232" |};
                 v_info := dummy_var_info |})
                (Papp2 (Omul Op_int)
                 (Pvar
                  {| gv :=
                    {| v_var :=
                      {| vtype := sint;
                       vname := "i.231" |};
                     v_info := dummy_var_info |};
                   gs := Slocal |})
                 (Pconst
                  (Zpos
                    (xO
                      (xI
                        (xO xH))))))])
              (xO
               (xI xH))
              ([Pvar
                {| gv :=
                  {| v_var :=
                    {| vtype :=
                      sarr
                       (xO
                         (xO
                           (xO
                             (xO
                               (xO
                                 (xI
                                   (xO
                                     (xO
                                       (xI
                                         xH)))))))));
                     vname := "m1.226" |};
                   v_info := dummy_var_info |};
                 gs := Slocal |};
               Psub (AAscale) (U64)
                (xO
                 (xI
                   (xO xH)))
                ({| gv :=
                  {| v_var :=
                    {| vtype :=
                      sarr
                       (xO
                         (xO
                           (xO
                             (xO
                               (xO
                                 (xI
                                   (xO
                                     (xO
                                       (xI
                                         xH)))))))));
                     vname := "m2t.230" |};
                   v_info := dummy_var_info |};
                 gs := Slocal |})
                (Papp2 (Omul Op_int)
                 (Pvar
                  {| gv :=
                    {| v_var :=
                      {| vtype := sint;
                       vname := "i.231" |};
                     v_info := dummy_var_info |};
                   gs := Slocal |})
                 (Pconst
                  (Zpos
                    (xO
                      (xI
                        (xO xH))))));
               Psub (AAscale) (U64)
                (xO
                 (xI
                   (xO xH)))
                ({| gv :=
                  {| v_var :=
                    {| vtype :=
                      sarr
                       (xO
                         (xO
                           (xO
                             (xO
                               (xO
                                 (xI
                                   (xO
                                     (xO
                                       (xI
                                         xH)))))))));
                     vname := "rest.232" |};
                   v_info := dummy_var_info |};
                 gs := Slocal |})
                (Papp2 (Omul Op_int)
                 (Pvar
                  {| gv :=
                    {| v_var :=
                      {| vtype := sint;
                       vname := "i.231" |};
                     v_info := dummy_var_info |};
                   gs := Slocal |})
                 (Pconst
                  (Zpos
                    (xO
                      (xI
                        (xO xH))))))]))]));
         MkI
          (dummy_instr_info)
          (Cassgn
           (Lvar
             {| v_var :=
               {| vtype :=
                 sarr
                  (xO
                    (xO
                      (xO
                        (xO
                          (xO
                            (xI
                              (xO
                                (xO
                                  (xI
                                    xH)))))))));
                vname := "res.228" |};
              v_info := dummy_var_info |})
           (AT_none)
           (sarr
            (xO
              (xO
                (xO
                  (xO
                    (xO
                      (xI
                        (xO
                          (xO
                            (xI xH))))))))))
           (Pvar
            {| gv :=
              {| v_var :=
                {| vtype :=
                  sarr
                   (xO
                     (xO
                       (xO
                         (xO
                           (xO
                             (xI
                               (xO
                                 (xO
                                   (xI
                                     xH)))))))));
                 vname := "pres.229" |};
               v_info := dummy_var_info |};
             gs := Slocal |}));
         MkI
          (dummy_instr_info)
          (Ccall (DoNotInline)
           ([Lvar
             {| v_var :=
               {| vtype :=
                 sarr
                  (xO
                    (xO
                      (xO
                        (xO
                          (xO
                            (xI
                              (xO
                                (xO
                                  (xI
                                    xH)))))))));
                vname := "res.228" |};
              v_info := dummy_var_info |}])
           (xI
            (xO xH))
           ([Pvar
             {| gv :=
               {| v_var :=
                 {| vtype :=
                   sarr
                    (xO
                      (xO
                        (xO
                          (xO
                            (xO
                              (xI
                                (xO
                                  (xO
                                    (xI
                                      xH)))))))));
                  vname := "rest.232" |};
                v_info := dummy_var_info |};
              gs := Slocal |};
            Pvar
             {| gv :=
               {| v_var :=
                 {| vtype :=
                   sarr
                    (xO
                      (xO
                        (xO
                          (xO
                            (xO
                              (xI
                                (xO
                                  (xO
                                    (xI
                                      xH)))))))));
                  vname := "res.228" |};
                v_info := dummy_var_info |};
              gs := Slocal |}]))];
       f_tyout :=
        [sarr
          (xO
            (xO
              (xO
                (xO
                  (xO
                    (xI
                      (xO
                        (xO
                          (xI xH)))))))))];
       f_res :=
        [{| v_var :=
           {| vtype :=
             sarr
              (xO
                (xO
                  (xO
                    (xO
                      (xO
                        (xI
                          (xO
                            (xO
                              (xI xH)))))))));
            vname := "res.228" |};
          v_info := dummy_var_info |}];
       f_extra := tt |});
     (xI (xO xH),
      {| f_info :=
        xI (xI xH);
       f_tyin :=
        [sarr
          (xO
            (xO
              (xO
                (xO
                  (xO
                    (xI
                      (xO
                        (xO
                          (xI xH)))))))));
         sarr
          (xO
            (xO
              (xO
                (xO
                  (xO
                    (xI
                      (xO
                        (xO
                          (xI xH)))))))))];
       f_params :=
        [{| v_var :=
           {| vtype :=
             sarr
              (xO
                (xO
                  (xO
                    (xO
                      (xO
                        (xI
                          (xO
                            (xO
                              (xI xH)))))))));
            vname := "m.233" |};
          v_info := dummy_var_info |};
         {| v_var :=
           {| vtype :=
             sarr
              (xO
                (xO
                  (xO
                    (xO
                      (xO
                        (xI
                          (xO
                            (xO
                              (xI xH)))))))));
            vname := "res.234" |};
          v_info := dummy_var_info |}];
       f_body :=
        [MkI
          (dummy_instr_info)
          (Cfor
           ({| v_var :=
              {| vtype := sint; vname := "i.235" |};
             v_info := dummy_var_info |})
           (((UpTo, Pconst Z0),
            Pconst
             (Zpos
               (xO
                 (xI
                   (xO xH))))))
           ([MkI
             (dummy_instr_info)
             (Cfor
              ({| v_var :=
                 {| vtype := sint;
                  vname := "j.236" |};
                v_info := dummy_var_info |})
              (((UpTo, Pconst Z0),
               Pconst
                (Zpos
                  (xO
                    (xI
                      (xO xH))))))
              ([MkI
                (dummy_instr_info)
                (Cassgn
                 (Lvar
                   {| v_var :=
                     {| vtype :=
                       sword U64;
                      vname := "tmp.237" |};
                    v_info := dummy_var_info |})
                 (AT_none) (sword U64)
                 (Pget (AAscale) (U64)
                  ({| gv :=
                    {| v_var :=
                      {| vtype :=
                        sarr
                         (xO
                           (xO
                             (xO
                               (xO
                                 (xO
                                   (xI
                                     (xO
                                       (xO
                                         (xI
                                           xH)))))))));
                       vname := "m.233" |};
                     v_info := dummy_var_info |};
                   gs := Slocal |})
                  (Papp2 (Oadd Op_int)
                   (Pvar
                    {| gv :=
                      {| v_var :=
                        {| vtype := sint;
                         vname := "j.236" |};
                       v_info := dummy_var_info |};
                     gs := Slocal |})
                   (Papp2 (Omul Op_int)
                    (Pvar
                     {| gv :=
                       {| v_var :=
                         {| vtype := sint;
                          vname := "i.235" |};
                        v_info := dummy_var_info |};
                      gs := Slocal |})
                    (Pconst
                     (Zpos
                       (xO
                         (xI
                           (xO xH)))))))));
               MkI
                (dummy_instr_info)
                (Cassgn
                 (Laset (AAscale)
                   (U64)
                   ({| v_var :=
                     {| vtype :=
                       sarr
                        (xO
                          (xO
                            (xO
                              (xO
                                (xO
                                  (xI
                                    (xO
                                      (xO
                                        (xI
                                          xH)))))))));
                      vname := "res.234" |};
                    v_info := dummy_var_info |})
                   (Papp2 (Oadd Op_int)
                    (Pvar
                     {| gv :=
                       {| v_var :=
                         {| vtype := sint;
                          vname := "i.235" |};
                        v_info := dummy_var_info |};
                      gs := Slocal |})
                    (Papp2 (Omul Op_int)
                     (Pvar
                      {| gv :=
                        {| v_var :=
                          {| vtype := sint;
                           vname := "j.236" |};
                         v_info := dummy_var_info |};
                       gs := Slocal |})
                     (Pconst
                      (Zpos
                        (xO
                          (xI
                            (xO xH))))))))
                 (AT_none) (sword U64)
                 (Pvar
                  {| gv :=
                    {| v_var :=
                      {| vtype :=
                        sword U64;
                       vname := "tmp.237" |};
                     v_info := dummy_var_info |};
                   gs := Slocal |}))]))]))];
       f_tyout :=
        [sarr
          (xO
            (xO
              (xO
                (xO
                  (xO
                    (xI
                      (xO
                        (xO
                          (xI xH)))))))))];
       f_res :=
        [{| v_var :=
           {| vtype :=
             sarr
              (xO
                (xO
                  (xO
                    (xO
                      (xO
                        (xI
                          (xO
                            (xO
                              (xI xH)))))))));
            vname := "res.234" |};
          v_info := dummy_var_info |}];
       f_extra := tt |});
     (xO (xI xH),
      {| f_info :=
        xO
         (xO (xO xH));
       f_tyin :=
        [sarr
          (xO
            (xO
              (xO
                (xO
                  (xO
                    (xI
                      (xO
                        (xO
                          (xI xH)))))))));
         sarr
          (xO
            (xO
              (xO
                (xO
                  (xI
                    (xO xH))))));
         sarr
          (xO
            (xO
              (xO
                (xO
                  (xI
                    (xO xH))))))];
       f_params :=
        [{| v_var :=
           {| vtype :=
             sarr
              (xO
                (xO
                  (xO
                    (xO
                      (xO
                        (xI
                          (xO
                            (xO
                              (xI xH)))))))));
            vname := "m.238" |};
          v_info := dummy_var_info |};
         {| v_var :=
           {| vtype :=
             sarr
              (xO
                (xO
                  (xO
                    (xO
                      (xI
                        (xO xH))))));
            vname := "v.239" |};
          v_info := dummy_var_info |};
         {| v_var :=
           {| vtype :=
             sarr
              (xO
                (xO
                  (xO
                    (xO
                      (xI
                        (xO xH))))));
            vname := "res.240" |};
          v_info := dummy_var_info |}];
       f_body :=
        [MkI
          (dummy_instr_info)
          (Cfor
           ({| v_var :=
              {| vtype := sint; vname := "i.241" |};
             v_info := dummy_var_info |})
           (((UpTo, Pconst Z0),
            Pconst
             (Zpos
               (xO
                 (xI
                   (xO xH))))))
           ([MkI
             (dummy_instr_info)
             (Ccall (DoNotInline)
              ([Lvar
                {| v_var :=
                  {| vtype :=
                    sword U64;
                   vname := "tmp.242" |};
                 v_info := dummy_var_info |}])
              (xI
               (xO
                 (xO xH)))
              ([Psub (AAscale) (U64)
                (xO
                 (xI
                   (xO xH)))
                ({| gv :=
                  {| v_var :=
                    {| vtype :=
                      sarr
                       (xO
                         (xO
                           (xO
                             (xO
                               (xO
                                 (xI
                                   (xO
                                     (xO
                                       (xI
                                         xH)))))))));
                     vname := "m.238" |};
                   v_info := dummy_var_info |};
                 gs := Slocal |})
                (Papp2 (Omul Op_int)
                 (Pvar
                  {| gv :=
                    {| v_var :=
                      {| vtype := sint;
                       vname := "i.241" |};
                     v_info := dummy_var_info |};
                   gs := Slocal |})
                 (Pconst
                  (Zpos
                    (xO
                      (xI
                        (xO xH))))));
               Pvar
                {| gv :=
                  {| v_var :=
                    {| vtype :=
                      sarr
                       (xO
                         (xO
                           (xO
                             (xO
                               (xI
                                 (xO xH))))));
                     vname := "v.239" |};
                   v_info := dummy_var_info |};
                 gs := Slocal |}]));
            MkI
             (dummy_instr_info)
             (Cassgn
              (Laset (AAscale) (U64)
                ({| v_var :=
                  {| vtype :=
                    sarr
                     (xO
                       (xO
                         (xO
                           (xO
                             (xI
                               (xO xH))))));
                   vname := "res.240" |};
                 v_info := dummy_var_info |})
                (Pvar
                 {| gv :=
                   {| v_var :=
                     {| vtype := sint;
                      vname := "i.241" |};
                    v_info := dummy_var_info |};
                  gs := Slocal |}))
              (AT_none) (sword U64)
              (Pvar
               {| gv :=
                 {| v_var :=
                   {| vtype :=
                     sword U64;
                    vname := "tmp.242" |};
                  v_info := dummy_var_info |};
                gs := Slocal |}))]))];
       f_tyout :=
        [sarr
          (xO
            (xO
              (xO
                (xO
                  (xI
                    (xO xH))))))];
       f_res :=
        [{| v_var :=
           {| vtype :=
             sarr
              (xO
                (xO
                  (xO
                    (xO
                      (xI
                        (xO xH))))));
            vname := "res.240" |};
          v_info := dummy_var_info |}];
       f_extra := tt |});
     (xI
       (xO (xO xH)),
      {| f_info :=
        xO
         (xI (xO xH));
       f_tyin :=
        [sarr
          (xO
            (xO
              (xO
                (xO
                  (xI
                    (xO xH))))));
         sarr
          (xO
            (xO
              (xO
                (xO
                  (xI
                    (xO xH))))))];
       f_params :=
        [{| v_var :=
           {| vtype :=
             sarr
              (xO
                (xO
                  (xO
                    (xO
                      (xI
                        (xO xH))))));
            vname := "v1.243" |};
          v_info := dummy_var_info |};
         {| v_var :=
           {| vtype :=
             sarr
              (xO
                (xO
                  (xO
                    (xO
                      (xI
                        (xO xH))))));
            vname := "v2.244" |};
          v_info := dummy_var_info |}];
       f_body :=
        [MkI
          (dummy_instr_info)
          (Cassgn
           (Lvar
             {| v_var :=
               {| vtype :=
                 sword U64;
                vname := "res.245" |};
              v_info := dummy_var_info |})
           (AT_none) (sword U64)
           (Papp1 (Oword_of_int U64)
            (Pconst Z0)));
         MkI
          (dummy_instr_info)
          (Cfor
           ({| v_var :=
              {| vtype := sint; vname := "i.246" |};
             v_info := dummy_var_info |})
           (((UpTo, Pconst Z0),
            Pconst
             (Zpos
               (xO
                 (xI
                   (xO xH))))))
           ([MkI
             (dummy_instr_info)
             (Cassgn
              (Lvar
                {| v_var :=
                  {| vtype :=
                    sword U64;
                   vname := "tmp.247" |};
                 v_info := dummy_var_info |})
              (AT_none) (sword U64)
              (Pget (AAscale) (U64)
               ({| gv :=
                 {| v_var :=
                   {| vtype :=
                     sarr
                      (xO
                        (xO
                          (xO
                            (xO
                              (xI
                                (xO xH))))));
                    vname := "v1.243" |};
                  v_info := dummy_var_info |};
                gs := Slocal |})
               (Pvar
                {| gv :=
                  {| v_var :=
                    {| vtype := sint;
                     vname := "i.246" |};
                   v_info := dummy_var_info |};
                 gs := Slocal |})));
            MkI
             (dummy_instr_info)
             (Cassgn
              (Lvar
                {| v_var :=
                  {| vtype :=
                    sword U64;
                   vname := "tmp.247" |};
                 v_info := dummy_var_info |})
              (AT_none) (sword U64)
              (Papp2
               (Omul (Op_w U64))
               (Pvar
                {| gv :=
                  {| v_var :=
                    {| vtype :=
                      sword U64;
                     vname := "tmp.247" |};
                   v_info := dummy_var_info |};
                 gs := Slocal |})
               (Pget (AAscale) (U64)
                ({| gv :=
                  {| v_var :=
                    {| vtype :=
                      sarr
                       (xO
                         (xO
                           (xO
                             (xO
                               (xI
                                 (xO xH))))));
                     vname := "v2.244" |};
                   v_info := dummy_var_info |};
                 gs := Slocal |})
                (Pvar
                 {| gv :=
                   {| v_var :=
                     {| vtype := sint;
                      vname := "i.246" |};
                    v_info := dummy_var_info |};
                  gs := Slocal |}))));
            MkI
             (dummy_instr_info)
             (Cassgn
              (Lvar
                {| v_var :=
                  {| vtype :=
                    sword U64;
                   vname := "res.245" |};
                 v_info := dummy_var_info |})
              (AT_none) (sword U64)
              (Papp2
               (Oadd (Op_w U64))
               (Pvar
                {| gv :=
                  {| v_var :=
                    {| vtype :=
                      sword U64;
                     vname := "res.245" |};
                   v_info := dummy_var_info |};
                 gs := Slocal |})
               (Pvar
                {| gv :=
                  {| v_var :=
                    {| vtype :=
                      sword U64;
                     vname := "tmp.247" |};
                   v_info := dummy_var_info |};
                 gs := Slocal |})))]))];
       f_tyout := [sword U64];
       f_res :=
        [{| v_var :=
           {| vtype := sword U64;
            vname := "res.245" |};
          v_info := dummy_var_info |}];
       f_extra := tt |})];
   p_globs := []; p_extra := tt |}
.