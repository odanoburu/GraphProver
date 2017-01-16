-------------------------------------------------------------------------------
--   Sequent Calculus Print Module
--
--   This module defines the functions for printing proofs in Latex.
--
--   @authors: jefferson
--
-------------------------------------------------------------------------------
require "Logic/SequentCalculus/SequentCalculusHelper"

local logger = logging.file("aux/prover%s.log", "%Y-%m-%d")
logger:setLevel(logging.INFO)

PrintModule = {}

local serializedSequent = ""

-- Private functions

local function printFormula(formulaNode, shortedFormula)
   local ret = ""
   local edge, subformula = nil
   
   if shortedFormula == nil then shortedFormula = true end
      
   local formulaNumber = formulaNode:getLabel():sub(6,formulaNode:getLabel():len())
   local formulaNumberCopied = nil
   
   local originalFormula = HelperModule.getOriginalFormulaCopied(formulaNode) --formulaNode:getInformation("originalFormula")
   if originalFormula ~= nil then
      formulaNumber = originalFormula:getLabel():sub(6,formulaNode:getLabel():len())
      formulaNumberCopied = formulaNode:getLabel():sub(6,formulaNode:getLabel():len())
   end

   if (formulaNode:getEdgesOut() ~= nil) and (#formulaNode:getEdgesOut() ~= 0) then
      if formulaNode:getInformation("type") == lblNodeFocus then
         ret = ret.."{\\color{red}\\{}"
         for i, edge in ipairs(formulaNode:getEdgesOut()) do
            subformula = edge:getDestino()
            ret = ret..printFormula(subformula, shortedFormula)..","
         end
         ret = ret:sub(1, ret:len()-1)
         ret = ret.."{\\color{red}\\}}"
      elseif formulaNode:getInformation("type") == lblNodeBrackets then
         ret = ret.."{\\color{red}[}"
         for i, edge in ipairs(formulaNode:getEdgesOut()) do
            subformula = edge:getDestino()
            ret = ret..printFormula(subformula, shortedFormula).."," --"^{"..edge:getLabel().."},"
         end
         ret = ret:sub(1, ret:len()-1)
         ret = ret.."{\\color{red}]}"
      else
         if not shortedFormula then
            for i, edge in ipairs(formulaNode:getEdgesOut()) do
               if edge:getLabel() == lblEdgeEsq then
                  subformula = edge:getDestino()
                  ret = ret.."("..printFormula(subformula, shortedFormula)
               end
            end
         end

         if originalFormula ~= nil then
            ret = ret.." "..opImp.tex.."_{"..formulaNumber.."}^{"..formulaNumberCopied.."}"
         else
            ret = ret.." "..opImp.tex.."_{"..formulaNumber.."}"
         end         

         if not shortedFormula then
            for i, edge in ipairs(formulaNode:getEdgesOut()) do
               if edge:getLabel() == lblEdgeDir then
                  subformula = edge:getDestino()
                  ret = ret..printFormula(subformula, shortedFormula)..")"
               end
            end
         end
      end
   else
      ret = formulaNode:getLabel()
      if formulaNode:getInformation("type") == lblNodeBrackets then
         ret = "{\\color{red}[]}"
      end
      if formulaNode:getInformation("type") == lblNodeFocus then
         ret = "{\\color{red}\\{\\}}"
      end      
   end

   return ret

end

local function printSequent(sequentNode, file, pprintAll)
   local ret = ""
   local edge, nodeEsq, nodeDir = nil
   local deductions = {}
   local j = 1
   local rule = ""
   local shortedFormula = false
   local alreadyPrintedFormulas = Set:new()

   if sequentNode ~= nil then

      if tonumber(sequentNode:getLabel():sub(4)) == 8 then
         local x = 10
      end          

      
      local seqNumber = sequentNode:getLabel():sub(4,sequentNode:getLabel():len())
      if seqNumber == "0" then shortedFormula = false end
      
      for i, edge in ipairs(sequentNode:getEdgesOut()) do       
         if edge:getLabel() == lblEdgeEsq then
            nodeEsq = edge:getDestino()
         end
         if edge:getLabel() == lblEdgeDir then
            nodeDir = edge:getDestino()
         end
         if edge:getLabel() == lblEdgeDeducao then
            local seqDed = edge:getDestino()
            deductions[j] = seqDed
            rule = edge:getInformation("rule")
            j = j+1
         end                    
      end
     
      if not sequentNode:getInformation("wasPrinted") or pprintAll then        
         if #deductions > 0 then
            file:write("\\infer["..rule.."]\n")
         end

         if sequentNode:getInformation("isAxiom") then
            file:write("{\\color{blue}{")
         else            
            file:write("{")
         end

         if sequentNode:getInformation("isProved") ~= nil and not sequentNode:getInformation("isProved") then
            file:write("{\\color{red}{")
         else            
            file:write("{")
         end        
         
         if nodeEsq ~= nil then
            for i, edge in ipairs(nodeEsq:getEdgesOut()) do
               local formulaNode = edge:getDestino()
               local atomicReference = edge:getInformation("reference") 
               
               local formulaAsStr = printFormula(formulaNode, shortedFormula)
               local contextAsStr = HelperModule.getOriginalFormulaCopied(formulaNode):getLabel()

               if atomicReference ~= nil then                                   
                  formulaAsStr = "("..formulaAsStr..")^{"..atomicReference:getLabel().."}"
                  contextAsStr = contextAsStr..atomicReference:getLabel()
               end
                                        
               if not alreadyPrintedFormulas:contains(contextAsStr) then
                  ret = ret..formulaAsStr
                  alreadyPrintedFormulas:add(contextAsStr)
                  ret = ret..","
               end              
            end    
            ret = ret:sub(1, ret:len()-1)
         end

         ret = ret.." {\\color{blue}"..opSeq.tex.."_{"..seqNumber.."}} "

         edge = nil
         for i, edge in ipairs(nodeDir:getEdgesOut()) do
            ret = ret..printFormula(edge:getDestino(), shortedFormula)
            ret = ret..","
         end       
         ret = ret:sub(1, ret:len()-1)     

         file:write(ret)
         if sequentNode:getInformation("isAxiom") then
            file:write("}}")
         else            
            file:write("}")
         end

         if sequentNode:getInformation("isProved") ~= nil and not sequentNode:getInformation("isProved") then
            file:write("}}")
         else            
            file:write("}")
         end     

         --serializedSequent = serializedSequent..ret.." "  

         if #deductions > 0 then
            --serializedSequent = serializedSequent:sub(1, serializedSequent:len()-1)
            --serializedSequent = serializedSequent.."|"
            file:write("\n{\n")

            for i, edge in ipairs(deductions) do               
               printSequent(deductions[i], file, pprintAll)
               if #deductions > 1 and i < #deductions then
                  file:write(" & ")
               end                 
            end

            file:write("\n}")
         end
      else
         local close = false
         if #deductions == 0 then
            if not sequentNode:getInformation("isAxiom") then
               file:write("\\infer["..rule.."]\n")
               file:write("{\\mbox{continuing} "..opSeq.tex.."_{"..seqNumber.."}}")
               file:write("\n{}")
               file:write("\\qquad\\qquad\r")
            end
         else            
            for i, edge in ipairs(deductions) do
               if not deductions[i]:getInformation("wasPrinted") then
                  file:write("\\infer["..rule.."]\n")
                  file:write("{\\mbox{continuing} "..opSeq.tex.."_{"..seqNumber.."}}")
                  file:write("\n{\n")
                  close = true
               end
               
               printSequent(deductions[i], file, pprintAll)
               if #deductions > 1 and i < #deductions then
                  -- file:write(" & ")
               end

               if close then
                  file:write("\n}")
                  file:write("\\qquad\\qquad\r")               
                  close = false
               end
            end
         end         
      end
            
      sequentNode:setInformation("wasPrinted", true)
   end
end

-- Public functions

function PrintModule.printProof(agraph, nameSufix, pprintAll)
   graph = agraph

   if nameSufix == nil then nameSufix = "" end
   
   local file = io.open("aux/prooftree"..nameSufix..".tex", "w")   
   local goalEdge = agraph:getNode(lblNodeGG):getEdgesOut()
   local ret = false

   if (goalEdge ~= nil) and (#goalEdge > 0) then
      
      local seq = goalEdge[1]:getDestino()

      file:write("\\documentclass[landscape]{article}\n\n")

      file:write("\\usepackage{amsbsy}\n")
      file:write("\\usepackage{color}\n")
      file:write("\\usepackage{proof}\n")
      file:write("\\usepackage{qtree}\n\n")
      file:write("\\usepackage{incgraph}\n\n")
      file:write("\\begin{document}\n")
      file:write("\\begin{inctext}\n")
      file:write("$$\n")      

      printSequent(seq, file, pprintAll)
      
      --serializedSequent = serializedSequent:gsub("\\vdash", "⊨")
      --serializedSequent = serializedSequent:gsub("\\to", "→")
      --logger:info("statistics -- Serialized sequent: "..serializedSequent)  
      --logger:info("statistics -- Size of serialized sequent: "..serializedSequent:len())  
      --countGraphElements()

      file:write("\n$$\n")
      file:write("\\end{inctext}\n")
      file:write("\\end{document}\n")
      file:close()

      ret = true
   end

   return ret
end
