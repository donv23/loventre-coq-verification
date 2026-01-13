import unittest

class TestExample(unittest.TestCase):
    def test_addition(self):
        # Test semplice per aggiungere 1+1
        self.assertEqual(1 + 1, 2)
        
    def test_multiplication(self):
        # Test per moltiplicare 2*2
        self.assertEqual(2 * 2, 4)

    def test_subtraction(self):
        # Test per sottrarre 3-1
        self.assertEqual(3 - 1, 2)

    def test_string_concatenation(self):
        # Test per concatenare stringhe
        self.assertEqual("Hello " + "World", "Hello World")

if __name__ == '__main__':
    unittest.main()

