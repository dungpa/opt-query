OptQuery - a query expression for optimization
===
### Built upon [Microsoft SolverFoundation's ODSL](http://blogs.msdn.com/b/lengningliu/archive/2009/09/04/optimization-domain-specific-language-in-f-with-units-of-measure.aspx) and F# 3.0's [custom keywords](http://msdn.microsoft.com/en-us/library/hh289709.aspx) ###

---
### Examples ###

```fsharp
let petrochem () =   
    opt { let! sa = var<Barrel/Day>()
          let! vz = var<_>()
          assume (0.3 * sa + 0.4 * vz >= 2000.<_>)
          assume (0.4 * sa + 0.2 * vz >= 1500.<_>)
          assume (0.2 * sa + 0.3 * vz >= 500.<_>)
          assume (sa <= 9000.<_> && sa >= 0.<_>)
          assume (vz <= 6000.<_> && vz >= 0.<_>)   
          minimise (20.0<Dollar/Barrel> * sa + 15.0<_> * vz)
    }
```
---
### Syntax ###
The language implemented in this sample has the following grammar: 

```fsharp
LinearProgram := (Variables, LinearConstraints, ObjectiveFunction)

Variables := Variable 
          := Variable \n Variables

Variable := let identifier = var       <UnitAnnotation>() 
         := let identifier = vararray1 <UnitAnnotation>(range) 
         := let identifier = vararray2 <UnitAnnotation>(range,range) 

ObjectiveFunction := minimise LinearFunction
                  := maximise LinearFunction

LinearFunction	:= RealConstant * RealVariable
                := LinearFunction + LinearFunction
                := sum range (fun identifier -> LinearFunction) 

LinearConstraints := LinearConstraint
                  := LinearConstraint \n LinearConstraints 

LinearConstraint := assume Constraint

Constraint := LinearFunction <= RealConstant
           := LinearFunction >= RealConstant
           := LinearFunction =  RealConstant
           := integral identifier
           := foreach range (fun identifier -> Constraint)

RealConstant := float_literal_constant
             := identifier
             := identifier.[Integer]
             := identifier.[Integer, Integer] 

RealVariable := identifier
             := identifier.[Integer]
             := identifier.[Integer, Integer]

Integer := integer_literal_constant
        := identifier
```
---
More details will be added later.
