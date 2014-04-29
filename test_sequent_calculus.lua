require 'parse_input'
require 'constants'
require 'utility'
require 'SequentCalculusLogic'

function testExpandAll(input)
   input_formula = parse_input(input)
   
   t_formula = stringtotable(input_formula)				

   SequentGraph,goalsList = LogicModule.createGraphFromTable(t_formula)
end

