--[[

   Server for data input.

   Author: Hermann
   Contributor: Jefferson

]]--

require "luarocks.loader"

require"parse_input"
require"socket"


local s = assert(socket.bind("localhost",8080))
local i, p = s:getsockname()

assert(i, p)

print("Waiting connection")

local user = assert(s:accept())
print("user connected")

while true do 
   local msg,stat = user:receive()
   if (stat == "closed") then 
      break 
   end

   if (msg == "read") then
      print("Enter new formula or type 'end' to finish:")
      input = io.read()
      if input == "end" then
	 break
      end
      p = parse_input(input)
      print(" no parser "..p)

      user:send(p..'\n')
   else
      if msg then 
	 print(msg)
      else 
	 print("nao recebeu")
      end
   end
end

