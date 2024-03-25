int aux = 2 + 3 * 5 / 10 >> 3 & 2 + 3 * 5 / 10 << 5 | 20 ^ 10 + 20 & 2 + 3 * 10 + 5 / 10;
int aux1 = 2 + aux * 5 / 10;
int aux2 = aux = aux1 = 2 + 3 * aux1 / 10;
return aux + 10;
