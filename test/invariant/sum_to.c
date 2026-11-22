int sum_to(unsigned n)
{
	unsigned i = 0;
	unsigned acc = 0;

	while (i < n) {
		acc += i;
		i++;
	}
	return (int)acc;
}
