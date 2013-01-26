OptQuery - a query expression for optimization
===
### Built upon [Microsoft SolverFoundation's ODSL](http://blogs.msdn.com/b/lengningliu/archive/2009/09/04/optimization-domain-specific-language-in-f-with-units-of-measure.aspx) and F# 3.0's [custom keywords](http://msdn.microsoft.com/en-us/library/hh289709.aspx) ###

---
### Syntax ###
The language implemented in this sample has the following grammar: 

LinearProgram	:= (Variables, ObjectiveFunction, LinearConstraints)

Variables 		:= Variable 
			:= Variable \n Variables

Variable 		:= let identifier = var       <UnitAnnotation>() 
			:= let identifier = vararray1 <UnitAnnotation>(range) 
			:= let identifier = vararray2 <UnitAnnotation>(range,range) 


ObjectiveFunction	:= minimise LinearFunction
:= maximise LinearFunction

LinearFunction	:= RealConstant * RealVariable
:= LinearFunction + LinearFunction
:= sum range (fun identifier -> LinearFunction) 

LinearConstraints		:= LinearConstraint
:= LinearConstraint \n LinearConstraints 

LinearConstraint := assume Constraint

Constraint		:= LinearFunction <= RealConstant
:= LinearFunction >= RealConstant
:= LinearFunction =  RealConstant
:= integral identifier
:= foreach range (fun identifier -> Constraint)


RealConstant	:= float_literal_constant
:= identifier
:= identifier.[Integer]
:= identifier.[Integer, Integer] 

RealVariable	:= identifier
:= identifier.[Integer]
:= identifier.[Integer, Integer]

Integer    		:= integer_literal_constant
:= identifier

---
More details will be added later.
