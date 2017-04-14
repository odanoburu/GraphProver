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
   local edge
   
   if shortedFormula == nil then shortedFormula = true end
      
   local formulaNumber = formulaNode:getLabel():sub(6,formulaNode:getLabel():len())
   local formulaNumberCopied = nil
   
   local originalFormula = HelperModule.getOriginalFormulaCopied(formulaNode)
   if originalFormula ~= nil then
      formulaNumber = originalFormula:getLabel():sub(6,formulaNode:getLabel():len())
      formulaNumberCopied = formulaNode:getLabel():sub(6,formulaNode:getLabel():len())
   end

   if (formulaNode:getEdgesOut() ~= nil) and (#formulaNode:getEdgesOut() ~= 0) then
      if formulaNode:getInformation("type") == lblNodeFocus then
         ret = ret.."{\\color{"..counterExampleColor.."}\\{}"
         for i, edge in ipairs(formulaNode:getEdgesOut()) do
            subformula = edge:getDestino()
            ret = ret..printFormula(subformula, shortedFormula)..","
         end
         ret = ret:sub(1, ret:len()-1)
         ret = ret.."{\\color{"..counterExampleColor.."}\\}}"
      elseif formulaNode:getInformation("type") == lblNodeBrackets then
         ret = ret.."{\\color{"..counterExampleColor.."}[}"
         for i, edge in ipairs(formulaNode:getEdgesOut()) do
            subformula = edge:getDestino()
            ret = ret..printFormula(subformula, shortedFormula)..","
         end
         ret = ret:sub(1, ret:len()-1)
         ret = ret.."{\\color{"..counterExampleColor.."}]}"
      else
         if not shortedFormula then
            for i, edge in ipairs(formulaNode:getEdgesOut()) do
               if edge:getLabel() == lblEdgeEsq then
                  subformula = edge:getDestino()
                  ret = ret.."("..printFormula(subformula, shortedFormula)
               end
            end
         end

         if originalFormula ~= nil and printCopiedId then
            ret = ret..opImp.tex.."_{"..formulaNumber.."}^{"..formulaNumberCopied.."}"
         else
            ret = ret..opImp.tex.."_{"..formulaNumber.."}"
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
         ret = "{\\color{"..counterExampleColor.."}[]}"
      end
      if formulaNode:getInformation("type") == lblNodeFocus then
         ret = "{\\color{"..counterExampleColor.."}\\{\\}}"
      end      
   end

   return ret

end

local function printSequent(sequentNode, printOnlyOpenBranch)
   local ret = ""
   local edge, nodeEsq, nodeDir = nil
   local deductions = {}
   local j = 1
   local rule = ""
   local shortedFormula = printShortedFormulas
   local alreadyPrintedFormulas = Set:new()

   if sequentNode ~= nil then

      -- to stop debug at a specific point
      if tonumber(sequentNode:getLabel():sub(4)) == 4 then
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

      if #deductions > 0 then
         ret = ret.."\\infer["..rule.."]\n"
      end      

      -- Conclusion

      if sequentNode:getInformation("isAxiom") then
         ret = ret.."{\\color{"..axiomColor.."}{"
      elseif sequentNode:getInformation("isProved") ~= nil and not sequentNode:getInformation("isProved") then
         ret = ret.."{\\color{"..counterExampleColor.."}{"
      else            
         ret = ret.."{"
      end      

      -- Left side
      if nodeEsq ~= nil then
         for i, edge in ipairs(nodeEsq:getEdgesOut()) do
            local formulaNode = edge:getDestino()
            local atomicReference = edge:getInformation("reference") 
            
            local formulaAsStr = printFormula(formulaNode, shortedFormula)
            local contextAsStr = HelperModule.getOriginalFormulaCopied(formulaNode):getLabel()

            if atomicReference ~= nil then
               if shortedFormula then
                  formulaAsStr = "("..formulaAsStr..")^{"..atomicReference:getLabel().."}"
               else
                  formulaAsStr = formulaAsStr.."^{"..atomicReference:getLabel().."}"
               end
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

      -- Sequent Symbol
      ret = ret.." {\\color{"..axiomColor.."}"..opSeq.tex.."_{"..seqNumber.."}} "


      -- Right Side
      edge = nil
      for i, edge in ipairs(nodeDir:getEdgesOut()) do
         ret = ret..printFormula(edge:getDestino(), shortedFormula)
         ret = ret..","
      end       
      ret = ret:sub(1, ret:len()-1)     

      if sequentNode:getInformation("isAxiom") or
         ( sequentNode:getInformation("isProved") ~= nil and not sequentNode:getInformation("isProved")) then
         ret = ret.."}}"
      else            
         ret = ret.."}"
      end

      --serializedSequent = serializedSequent..ret.." "  
      if #deductions > 0 then
         --serializedSequent = serializedSequent:sub(1, serializedSequent:len()-1)
         --serializedSequent = serializedSequent.."|"

         ret = ret.."{\n"
         
         for i, nextSeqNode in ipairs(deductions) do
            if printOnlyOpenBranch then
               -- Print dots in the branch that is not totally expanded or is closed.
               if sequentNode:getInformation("isProved") or nextSeqNode:getInformation("isProved") ==nil then
                  ret = ret.."\\vdots"
               else
                  ret = ret..printSequent(deductions[i], printOnlyOpenBranch)
               end
            else
               ret = ret..printSequent(deductions[i], printOnlyOpenBranch)
            end
            
            if #deductions > 1 and i < #deductions then
               ret = ret.." & "
            end   
         end
         ret = ret.."}\n"         
      end
      
   end

   return ret
end

-- Public functions

function PrintModule.printGraph(agraph)
   local file = io.open("aux/proofgraph.dot", "w")

   local ret = agraph:toString()

   if ret ~= "" then 
      file:write(ret)
   end

   file:close()
end

function PrintModule.printProof(object, nameSufix, ppType)

   if ppType == nil then ppType = ppProof end   
   if nameSufix == nil then nameSufix = "1" end
   
   local texOutput = defaultOutput
   
   local file = io.open("aux/prooftree"..nameSufix..".tex", "w")
   local ret = false
   local content = ""

   file:write("\\documentclass[landscape]{article}\n\n")

   file:write("\\usepackage{etex}\n")      
   file:write("\\usepackage{amsbsy}\n")
   file:write("\\usepackage{color}\n")
   file:write("\\usepackage{proof}\n")
   
   if texOutput == texOutputPDF then
      file:write("\\usepackage{incgraph}\n\n")
   end 
   file:write("\\begin{document}\n")
   if texOutput == texOutputPDF then
      file:write("\\begin{inctext}\n")
   end

   if ppType == ppProof then
      local goalEdge = object:getNode(lblNodeGG):getEdgesOut()

      
      if (goalEdge ~= nil) and (#goalEdge > 0) then
         
         local seq = goalEdge[1]:getDestino()

         if seq:getEdgeOut(lblEdgeDeducao) ~= nil then
            content = content.."$$\n"
         else
            content = content.."$"
         end

         -- If Seq0 is false, print only the open branch
         if seq:getInformation("isProved") ~= nil and not seq:getInformation("isProved") then
            printOnlyOpenBranch = true
         else
            printOnlyOpenBranch = false         
         end
         
         content = content..printSequent(seq, printOnlyOpenBranch)
         
         --serializedSequent = serializedSequent:gsub("\\vdash", "⊨")
         --serializedSequent = serializedSequent:gsub("\\to", "→")
         --logger:info("statistics -- Serialized sequent: "..serializedSequent)  
         --logger:info("statistics -- Size of serialized sequent: "..serializedSequent:len())  
         --countGraphElements()
         
         if seq:getEdgeOut(lblEdgeDeducao) ~= nil then
            content = content.."\n$$\n"
         else
            content = content.."$\n"
         end
      end
   elseif ppType == ppSeq then
      if object:getEdgeOut(lblEdgeDeducao) ~= nil then
         content = content.."$$\n"
      else
         content = content.."$"
      end
      
      content = content..printSequent(object, printOnlyOpenBranch)

      if object:getEdgeOut(lblEdgeDeducao) ~= nil then
         content = content.."\n$$\n"
      else
         content = content.."$\n"
      end      

   elseif ppType == ppFormula then
      content = "$"..printFormula(object, printShortedFormulas).."$\n"      
   end

   file:write(content)
   
   if texOutput == texOutputPDF then
      file:write("\\end{inctext}\n")
   end
   file:write("\\end{document}\n")
   file:close()

   ret = true
   os.showProof(nameSufix)

   
   return ret
end
