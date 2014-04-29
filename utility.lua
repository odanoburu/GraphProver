--[[

   Utility Module

   Contain functions that can be used by all the aplication. Normaly functions for string manipulation or for debuging.
   This is provided by the grafic module to all others that want to use this functions.

   Author: Vitor

]]--

--[[
   Print in the screen all the messages contained in the MedDebugTable.
]]--
function printDebugMessageTable(client)
   for i = 1, #MsgDebugTable do
      if client then 
	 client:send(MsgDebugTable[i].."\n")
      end
   end
end

--[[
   Insert a message in the MsgDebugTable.
   Only insert diferents debug messages. This precaution was taken because of this function can be called
   by love.draw, so a span could occur.
   Param:
   debugMessage: A string containing the debug message.
]]--
function createDebugMessage(debugMessage)
   MsgDebugTable[#MsgDebugTable+1] = debugMessage
end

function clearDebugMessages()
   MsgDebugTable = {}
   MsgDebugTable[1] = "Prover debug messages:-----------------------------------"
end

function stringtotable(s)
   local t = {}
   
   if s == nil then
      return
   end
   
   createDebugMessage("entrou no stringtotable s="..s)
   for k in string.gmatch(s, "(%b[])") do
      v1=string.match(k,"%[%s*([^=]+)=.+")
      if v1 =="tag" then
	 v1,v2= string.match(k,"%[%s*([^=]+)=(%S+)%s")
	 t[v1]=v2
      else
	 if v1 then 
	    createDebugMessage("v1="..v1)
	    v2=string.match(k,"(%b{})")
	    if v2 then 
	       createDebugMessage("v2="..v2)
	       t[v1] = stringtotable(v2,client)
	    else
	       v2=string.match(k,"[^=]+=%s*(%S+)%s*%]")
	       if v2 then
		  createDebugMessage("v2="..v2) 
	       end
	       t[v1]= v2
	    end
	 end
      end
   end
   return(t)
end
