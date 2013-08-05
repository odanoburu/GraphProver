require('socket') -- sempre o require
local client = socket.connect('localhost',1234)
if client then
    print('Conectado')
else 
    print('offline')
    os.exit()
end
print('Escreva algo')
repeat
    client:send(io.read()..'\n')
until not client