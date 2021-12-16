@2
D = A // adresa na koju spremamo

@R0 // baza
M = D

@R2 // eksponent
M = D

@10
D = A

@R1
M = D

@y // privremena varijabla
M = 0

@brojac 
M = D - 1

// iteriramo kroz petlju i smanjujemo brojac 
// while petlja se izvodi dok brojac != 0

// while prima adresu R(??)

$WHILE(brojac)  // brojac se smanjuje dok nije 0

    @R0
    D = M

    @i
    M = D - 1 

    @R2
    D = M

    @y
    M = D 

    (START)
    $SUM(R2,y,R2) 

    @i
    M = M - 1 
    D = M 

    @START
    D;JNE //  != 0

    @brojac
    M = M - 1 // smanji adresu 

$END

