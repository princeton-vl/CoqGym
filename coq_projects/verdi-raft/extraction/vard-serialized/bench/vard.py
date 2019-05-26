import socket
import re
from uuid import uuid4
from select import select
from struct import pack, unpack

def poll(sock, timeout):
    return sock in select([sock], [], [], timeout)[0]

class SendError(Exception):
    pass

class ReceiveError(Exception):
    pass

class LeaderChanged(Exception):
    pass

class Client(object):
    class NoLeader(Exception):
        pass

    @classmethod
    def find_leader(cls, cluster):
        # cluster should be a list of [(host, port)] pairs
        for (host, port) in cluster:
            c = cls(host, port)
            try:
                c.get('a')
            except LeaderChanged:
                continue
            else:
                return (host, port)
        raise cls.NoLeader
    
    response_re = re.compile(r'Response\W+([0-9]+)\W+([/A-Za-z0-9]+|-)\W+([/A-Za-z0-9]+|-)\W+([/A-Za-z0-9]+|-)')

    def __init__(self, host, port, sock=None):
        self.client_id = uuid4().hex
        self.request_id = 0
        if sock is None:
            self.sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            self.sock.connect((host, port))
        else:
            self.sock = sock
        self.send_client_id()

    def send_client_id(self):
        n = self.sock.send(pack("<I", len(self.client_id)))
        if n < 4:
            raise SendError
        else:
            self.sock.send(self.client_id)

    def reconnect(self, host, port, sock=None):
        self.sock.shutdown(1)
        self.sock.close()
        if sock is None:
            self.sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            self.sock.connect((host, port))
        else:
            self.sock = sock
        self.send_client_id()
        
    def deserialize(self, data):
        if data == '-':
            return None
        return data

    def serialize(self, arg):
        if arg is None:
            return '-'
        return str(arg)

    def send_command(self, cmd, arg1=None, arg2=None, arg3=None):
        msg = str(self.request_id) + ' ' + cmd + ' ' + ' '.join(map(self.serialize, (arg1, arg2, arg3)))
        n = self.sock.send(pack("<I", len(msg)))
        if n < 4:
            raise SendError
        else:
            self.sock.send(msg)
            self.request_id += 1

    def parse_response(self, data):
        if data.startswith('NotLeader'):
            raise LeaderChanged
        try:
            match = self.response_re.match(data)
            return [self.deserialize(match.group(n)) for n in (1,2,3,4)]
        except Exception as e:
            print "Parse error, data=%s" % data
            raise e
        
    def process_response(self):
        len_bytes = self.sock.recv(4)
        if len_bytes == '':
            raise ReceiveError
        else:
            len_msg = unpack("<I", len_bytes)[0]
            data = self.sock.recv(len_msg)
            if data == '':
                raise ReceiveError
            else:
                return self.parse_response(data)

    def get(self, k):
        self.send_command('GET', k)
        return self.process_response()[2]

    def get_no_wait(self, k):
        self.send_command('GET', k)

    def put_no_wait(self, k, v):
        self.send_command('PUT', k, v)

    def put(self, k, v):
        self.send_command('PUT', k, v)
        return self.process_response()[2]

    def delete(self, k):
        self.send_command('DEL', k)
        self.process_response()[2]

    def compare_and_set(self, k, current, new):
        self.send_command('CAS', k, current, new)
        if self.process_response()[3] == new:
            return True
        return False

    def compare_and_delete(self, k, current):
        self.send_command('CAD', k, current)
        if self.process_response()[3] is None:
            return True
        return False
