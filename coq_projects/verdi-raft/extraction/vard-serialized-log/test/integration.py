import os, sys, subprocess, shutil
import unittest
sys.path.append(os.path.realpath(os.path.join(
    os.path.dirname(os.path.realpath(__file__)), '..', 'bench')))
from vard import Client
import time

VARDSERLOG = os.path.join(os.path.dirname(os.path.realpath(__file__)), '..', 'vardserlog.native')

class TestVard(unittest.TestCase):
    client = None
    processes = None

    def startProcesses(self):
        self.processes = []
        for i in range(3):
            port = 8000 + i
            args = [VARDSERLOG,
                    '-dbpath', 'db-%d' % i,
                    '-port', '%d' % port,
                    '-node', '0,localhost:9000',
                    '-node', '1,localhost:9001',
                    '-node', '2,localhost:9002',
                    '-me', '%d' % i]
            FNULL = open(os.devnull, 'w')
            proc = subprocess.Popen(args, stdout=FNULL, stderr=subprocess.STDOUT, close_fds=True)
            self.processes.append(proc)
            time.sleep(1)

    def connectClient(self):
        cluster = [('localhost', 8000),
                   ('localhost', 8001),
                   ('localhost', 8002)]
        host, port = Client.find_leader(cluster)
        self.client = Client(host, port)

    def terminateProcesses(self):
        for i in range(3):
            self.processes[i].terminate()
        self.client = None
        self.processes = None

    def removeProcessDirs(self):
        for i in range(3):
            shutil.rmtree('db-%d' % i)

    def setUp(self):
        """Start up a cluster"""
        self.startProcesses()
        self.connectClient()

    def tearDown(self):
        self.terminateProcesses()
        self.removeProcessDirs()

    def test_put_get(self):
       self.client.put('answer', '42')
       self.assertEqual(self.client.get('answer'), '42')

    def test_crash(self):
       self.client.put('answer', '42')
       self.client.put('plse', 'lab')
       self.client.put('average', 'joe')
       self.terminateProcesses()
       self.startProcesses()
       self.connectClient()
       self.assertEqual(self.client.get('answer'), '42')
       self.assertEqual(self.client.get('plse'), 'lab')
       self.assertEqual(self.client.get('average'), 'joe')
    
    def test_put_delete_get(self):
        self.client.put('answer', '42')
        self.client.delete('answer')
        self.assertEqual(self.client.get('answer'), None)

if __name__ == '__main__':
    unittest.main()

