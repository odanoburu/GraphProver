--[[

   Utility Module

   Contain functions that can be used by all the aplication. Normaly functions for string manipulation or for debuging.
   This is provided by the grafic module to all others that want to use this functions.

   Author: Vitor
   Contributors: Jefferson

]]--

function stringtotable(s)
   local t = {}
   
   if s == nil then
      return
   end
   
   for k in string.gmatch(s, "(%b[])") do
      v1=string.match(k,"%[%s*([^=]+)=.+")
      if v1 =="tag" then
	 v1,v2= string.match(k,"%[%s*([^=]+)=(%S+)%s")
	 t[v1]=v2
      else
	 if v1 then 
	    v2=string.match(k,"(%b{})")
	    if v2 then 
	       t[v1] = stringtotable(v2,client)
	    else
	       v2=string.match(k,"[^=]+=%s*(%S+)%s*%]")
	       t[v1]= v2
	    end
	 end
      end
   end
   return(t)
end


function os.capture()
   local f = assert(io.popen('uname', 'r'))
   local s = assert(f:read('*a'))
   f:close()
   s = string.gsub(s, '^%s+', '')
   s = string.gsub(s, '%s+$', '')
   s = string.gsub(s, '[\n\r]+', ' ')
   return s
end

function Set(t)
  local s = {}
  for _,v in pairs(t) do s[v] = true end
  return s
end

function contains(t, e)
  return t[e]
end
