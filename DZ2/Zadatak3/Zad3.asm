@i
M = 0  

(LOOP_START)
    
    @i
    A = M // odi na adresu
    D = M // dohvati broj
    
    @max  // max = vr
    M = D
    

    (LOOP)
    @i
    D = M // dohvati i

    @4
    D = A - D // 4 - i
    
    @LOOP_END
    D; JLE // <= 0  
    
    

    @max
    D = M // dohvati max
    
    @i
    M = M + 1  // povecaj i
    A = M     // iduca adresa
    D = M - D  // vr - max
    
    
    

    @LOOP_START
    D; JGT  // >0
    
    @LOOP
    0; JMP
    
(LOOP_END)

@max
D = M

@R5
M = D // zapisi max

(END)
@END
0; JMP
