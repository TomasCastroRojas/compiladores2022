# Compiladores
Código para la materia Compiladores 2022 de [LCC](https://dcc.fceia.unr.edu.ar), [FCEIA](https://www.fceia.unr.edu.ar), [UNR](https://www.unr.edu.ar).

Este es el código a partir del cual los estudiantes empiezan a desarrollar un compilador.

Para fijar la versión de GHC y de los paquetes usaremos la herramienta [stack](https://docs.haskellstack.org/en/stable/README/).

Los pasos para instalar son:

```code
stack setup
stack build
```

Luego se puede ejecutar con 
```code
stack run
```
o cargar el entorno interactivo GHCi
```code
stack ghci

stack ghci src/TypeChecker.hs
```

También se pueden cargar archivos. Desde stack:
```code
stack run -- miprograma.fd4
```

En general, los argumentos a nuestro programa se escriben luego de `--`. Por ejemplo,
```code
% stack run -- --help
Compilador de FD4 de la materia Compiladores 2022

Usage: compiladores-exe [(-t|--typecheck) | (-k|--CEK) | (-m|--bytecompile) | 
                          (-r|--runVM) | (-i|--interactive) | (-e|--eval) | 
                          (-c|--cc)] [-o|--optimize] [FILES...]
  Compilador de FD4

Available options:
  -t,--typecheck           Chequear tipos e imprimir el término
  -k,--CEK                 Ejecutar en la CEK
  -m,--bytecompile         Compilar a la BVM
  -r,--runVM               Ejecutar bytecode en la BVM
  -i,--interactive         Ejecutar en forma interactiva
  -e,--eval                Evaluar programa
  -c,--cc                  Compilar a código C
  -o,--optimize            Optimizar código
  -h,--help                Show this help text
```
Para compilar a Bytecode debe hacerse del siguiente modo
```code
stack run -- -m miprograma.fd4
```
Esto crea un archivo con el mismo nombre pero extension `.bc`
Para ejecutar hay dos opciones. Utilizar la maquina abstracta en `Haskell` o en `C`.
En `Haskell` es simplemente
```code
stack run -- -r miprograma.bc
```
En cambio en `C`, primero debemos compilar la maquina. Se encuentra en el directorio `vm`. Instructivo [aquí](https://github.com/TomasCastroRojas/compiladores2022/blob/main/vm/README.md)
Finalmente ejecutamos
```code
vm/macc miprograma.bc
```
Otra opción es compilar programas `fd4` a lenguaje `C`. Para esto
```code
stack run -- -c miprograma.fd4
```
Esto crea el mismo programa pero con extension `.c`. Luego compilamos con `gcc`
```code
gcc runtime.c -lgc miprograma.c

gcc -o miejecutable runtime.c -lgc miprograma.c
```
Ejecutamos
```code
./a.out

./miejecutable
```
Por último, se incluye una suit de tests para verificar que todos los backends coincidan en el resultado. Para correr los tests
```code 
make test
```
