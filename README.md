could do:
- [ ] fare in modo di parsare lo zucchero sintattico (do, then, else)
- [ ] fare >=, <=

per tenere tuple:
- 2 liste di liste:
    - 1 lista tiene le triple
    - 1 lista tiene i "figli" delle triple (precondizioni) tramite index 


>[!example] ESEMPIO:
> 
> ho un seq
> 
> {Q} x := x+1; x := x*2; {x = 10}
> 
> lista1 = [ 
>     {Q} x := x+1; x := x*2; {x = 10} 
>     
>     ]
> 
> questa genera due triple:
> 
> {Q} x := 2 {x = 10}
> 
> che quindi appendiamo in lista1
> 
> lista1 = [ 
>     {Q} x := x+1; x := x*2; {x = 10},
> 
>     {Q} x := 2 {x = 10}
>     
> ]
> 
> e, in lista2, la inseriamo come sua "figlia" 
> 
> (visto che la nostra tripla ha indice 0 e quella nuova indice 1, lista2 sarà)
> 
> lista2 = [ 
>     [ 1 ], (la tripla di indice 0 (in lista1) ha come "figlia" quella di indice 1)
> 
>     []
>     
> ]