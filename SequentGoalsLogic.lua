--[[

   Sequent Goals Logic Module

   Author: Vitor

]]--

require "SequentGraph"
require "Goal"

-- Junta as funções que este modulo oferece como publicas.
GoalsLogic = {}

-------------------------------------------- Public functions --------------------------------------------
function GoalsLogic.assembleGoalList(sequent)

   if goalsList == nil then
      goalsList = {}
   end
   
   assert( getmetatable(sequent) == Node_Metatable, "GoalsLogic.assembleGoalList: sequent must not be a node.")
   
   local newGoal = nil	

   local esqNode = sequent:getEdgeOut(lblEdgeEsq):getDestino()
   local dirNode = sequent:getEdgeOut(lblEdgeDir):getDestino()

   local j = 1
   
   local leftGoals = {}
   local esqEdges = esqNode:getEdgesOut()
   
   if esqEdges ~= nil then
      for i=1, #esqEdges do
	 local nodeEsq = esqEdges[i]:getDestino()
	 local typeOfNode = nodeEsq:getInformation("type")
	 
	 --if typeOfNode == opAnd.graph or typeOfNode == opOr.graph or typeOfNode == opImp.graph or typeOfNode == opNot.graph then
	 leftGoals[j] = nodeEsq
	 j = j + 1
	 --end
      end
   end	
   j = 1
   local rightGoals = {}
   local dirEdges = dirNode:getEdgesOut()
   if dirEdges ~= nil then 
      for i=1, #dirEdges do
	 local nodeDir = dirEdges[i]:getDestino()
	 local typeOfNode = nodeDir:getInformation("type")
	 
	 --if typeOfNode == opAnd.graph or typeOfNode == opOr.graph or typeOfNode == opImp.graph or typeOfNode == opNot.graph then
	 rightGoals[j] = nodeDir
	 j = j + 1
	 --end
      end
   end
   newGoal = Goal:new (sequent, leftGoals, rightGoals)

   -- A politica abaixo de gerenciamento da estrategia nao deve ser seguida (Hermann 31-12-2012)		
   -- Monto para o primeiro sequente a lista de goals, vendo quais operadores os nós do lado direito e esquerdo dele alcancam.
   
   -- Soh vou ter os sequentes correntes na lista de goals.
   
   -- Sempre que eu expandir um sequente a lista de goals associada a ele vai ser destruida.

   ---  O terceiro item acima deve implementar a remocao do goal que foi expandido (em left ou right) e nao as listas de goals do sequent usado na expancao, deve-de considerar falha na escolha e nova alternativa, alem de propagar os goals para os sequentes expandidos a partir do goal removido...			

   return newGoal
end
