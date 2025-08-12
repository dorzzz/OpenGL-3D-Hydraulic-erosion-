#include <cmath>
#include <cstdio>
#include <vector>
#include <algorithm>
#include <chrono>
#include <cstdlib>
#include <ctime>
#include "glut.h"

using namespace std::chrono;

constexpr double PI = 3.141592653589793;
constexpr int    GSZ = 100;

double ground[GSZ][GSZ] = { 0 };
double tmp[GSZ][GSZ] = { 0 };
constexpr double MIN_TERRAIN_HEIGHT = -20.0;
constexpr double SEA_LEVEL = 0.0;

double flow[GSZ][GSZ] = { 0 };
constexpr double FLOW_THR = 0.02;

constexpr double SAFE_MARGIN = 0.3;
constexpr double FLAT_MAX_DELTA = 0.45;
constexpr double BANK_MAX_RISE = 1.20;
constexpr double MAX_ELEV_FOR_HOUSE = 2.20;
constexpr int    FLAT_RADIUS = 1;

constexpr int CITY_RADIUS_CELLS = 8;
constexpr int CITY_MIN_SPACING = 3;
constexpr int CITY_CANDIDATE_TRIES = 2000;

bool   erosionActive = false, erosionStarted = false;
int    erosionCounter = 0;
constexpr int MAX_EROSION_STEPS = 100000;
steady_clock::time_point lastErosionTime;
int    erosionDelayMs = 10;

constexpr int    DROPLET_LIFE = 250;
int              dropletsPerFrame = 20;
constexpr double GRAVITY = 25.0;
constexpr double EVAPORATION = 0.06;
constexpr double DEPOSITION = 0.5;
constexpr double EROSION = 0.03;
constexpr double CAPACITY_K = 2.0;
constexpr double MIN_CAP = 1e-4;
constexpr double INERTIA_K = 0.25;
constexpr double FRICTION = 0.10;
constexpr double MAX_ERODE_PER_STEP = 0.02;
constexpr double MAX_DEPOSIT_PER_STEP = 0.005;
constexpr double SLOPE_DEPO_LIMIT = 0.25;

constexpr int ERODE_BRUSH_R = 1;
constexpr int DEPO_BRUSH_R = 2;

// camera
double speed = 0, angular_speed = 0, sight_angle = PI;
double dir[3] = { std::sin(PI), -0.3, std::cos(PI) };
double eye[3] = { 5, 18, 15 };

// houses
struct House { int x, y; double size, rotDeg, hscale; };
std::vector<House> houses;
bool housesPlaced = false;
constexpr int MAX_HOUSES = 10;

inline double dclamp(double v, double lo, double hi) { return v < lo ? lo : (v > hi ? hi : v); }

double SampleHeight(double x, double y)
{
	int ix = (int)std::floor(x), iy = (int)std::floor(y);
	ix = (int)dclamp(ix, 0, GSZ - 2);
	iy = (int)dclamp(iy, 0, GSZ - 2);
	double fx = x - ix, fy = y - iy;

	double h00 = ground[iy][ix];
	double h10 = ground[iy][ix + 1];
	double h01 = ground[iy + 1][ix];
	double h11 = ground[iy + 1][ix + 1];

	double hx0 = h00 * (1.0 - fx) + h10 * fx;
	double hx1 = h01 * (1.0 - fx) + h11 * fx;
	return hx0 * (1.0 - fy) + hx1 * fy;
}

void SampleGradient(double x, double y, double& gx, double& gy)
{
	const double eps = 0.5;
	gx = (SampleHeight(x + eps, y) - SampleHeight(x - eps, y)) * 0.5;
	gy = (SampleHeight(x, y + eps) - SampleHeight(x, y - eps)) * 0.5;
}


void Smooth()
{
	for (int i = 1; i < GSZ - 1; i++)
		for (int j = 1; j < GSZ - 1; j++)
			tmp[i][j] = (ground[i - 1][j - 1] + ground[i - 1][j] + ground[i - 1][j + 1] +
				ground[i][j - 1] + ground[i][j] + ground[i][j + 1] +
				ground[i + 1][j - 1] + ground[i + 1][j] + ground[i + 1][j + 1]) / 9.0;

	for (int i = 1; i < GSZ - 1; i++)
		for (int j = 1; j < GSZ - 1; j++)
			ground[i][j] = tmp[i][j];
}

void SetupTerrain(int num)
{
	double delta = 0.1;
	for (int k = 0; k < num; k++) {
		int x1 = rand() % GSZ, y1 = rand() % GSZ;
		int x2 = rand() % GSZ, y2 = rand() % GSZ;
		if ((k & 1) == 0) delta = -delta;
		if (x1 == x2) continue;

		double a = (y2 - y1) / ((double)x2 - x1);
		double b = y1 - a * x1;
		for (int i = 0; i < GSZ; i++)
			for (int j = 0; j < GSZ; j++)
				ground[i][j] += (i < a * j + b) ? delta : -delta;
	}
}

void SetColor(double h)
{
	double v = std::fabs(h);
	if (v < 0.3) glColor3d(0.9, 0.9, 0.7);
	else if (v < 2.0) glColor3d(0.2 + v / 5.0, 0.8 - v / 4.0, 0);
	else if (v < 4.0) glColor3d(v / 5.0, v / 5.0, v / 6.0);
	else              glColor3d(v / 5.5, v / 5.5, v / 5.0);
}

void ApplyErosionBrush(int cx, int cy, double amount)
{
	static double W[2 * ERODE_BRUSH_R + 1][2 * ERODE_BRUSH_R + 1];
	static bool init = false;
	if (!init) {
		double sum = 0;
		for (int dy = -ERODE_BRUSH_R; dy <= ERODE_BRUSH_R; ++dy)
			for (int dx = -ERODE_BRUSH_R; dx <= ERODE_BRUSH_R; ++dx) {
				double r = std::sqrt(double(dx * dx + dy * dy));
				double w = std::max(0.0, 1.0 - r / (ERODE_BRUSH_R + 1e-4));
				W[dy + ERODE_BRUSH_R][dx + ERODE_BRUSH_R] = w; sum += w;
			}
		for (int y = 0; y < 2 * ERODE_BRUSH_R + 1; y++)
			for (int x = 0; x < 2 * ERODE_BRUSH_R + 1; x++) W[y][x] /= sum;
		init = true;
	}

	for (int dy = -ERODE_BRUSH_R; dy <= ERODE_BRUSH_R; ++dy)
		for (int dx = -ERODE_BRUSH_R; dx <= ERODE_BRUSH_R; ++dx) {
			int x = cx + dx, y = cy + dy;
			if (x <= 0 || x >= GSZ - 1 || y <= 0 || y >= GSZ - 1) continue;
			double take = amount * W[dy + ERODE_BRUSH_R][dx + ERODE_BRUSH_R];
			double minH = MIN_TERRAIN_HEIGHT + 0.2;
			double available = std::max(0.0, ground[y][x] - minH);
			ground[y][x] -= std::min(take, available);
		}
}

void ApplyDepositionBrush(int cx, int cy, double amount)
{
	static double W[2 * DEPO_BRUSH_R + 1][2 * DEPO_BRUSH_R + 1];
	static bool init = false;
	if (!init) {
		double sum = 0;
		for (int dy = -DEPO_BRUSH_R; dy <= DEPO_BRUSH_R; ++dy)
			for (int dx = -DEPO_BRUSH_R; dx <= DEPO_BRUSH_R; ++dx) {
				double r = std::sqrt(double(dx * dx + dy * dy));
				double w = std::max(0.0, 1.0 - r / (DEPO_BRUSH_R + 1e-4));
				W[dy + DEPO_BRUSH_R][dx + DEPO_BRUSH_R] = w; sum += w;
			}
		for (int y = 0; y < 2 * DEPO_BRUSH_R + 1; y++)
			for (int x = 0; x < 2 * DEPO_BRUSH_R + 1; x++) W[y][x] /= sum;
		init = true;
	}

	for (int dy = -DEPO_BRUSH_R; dy <= DEPO_BRUSH_R; ++dy)
		for (int dx = -DEPO_BRUSH_R; dx <= DEPO_BRUSH_R; ++dx) {
			int x = cx + dx, y = cy + dy;
			if (x <= 0 || x >= GSZ - 1 || y <= 0 || y >= GSZ - 1) continue;
			ground[y][x] += amount * W[dy + DEPO_BRUSH_R][dx + DEPO_BRUSH_R];
		}
}

void ThermalRelax(int cx, int cy)
{
	constexpr double TALUS = 0.6, K = 0.5;
	for (int y = cy - 1; y <= cy + 1; ++y)
		for (int x = cx - 1; x <= cx + 1; ++x) {
			if (x <= 0 || x >= GSZ - 1 || y <= 0 || y >= GSZ - 1) continue;
			for (int dy = -1; dy <= 1; ++dy)
				for (int dx = -1; dx <= 1; ++dx) {
					if (!dx && !dy) continue;
					int nx = x + dx, ny = y + dy;
					if (nx <= 0 || nx >= GSZ - 1 || ny <= 0 || ny >= GSZ - 1) continue;
					double diff = ground[y][x] - ground[ny][nx];
					if (diff > TALUS) {
						double m = (diff - TALUS) * 0.5 * K;
						ground[y][x] -= m;
						ground[ny][nx] += m;
					}
				}
		}
}


struct Droplet { double x, y, vx, vy, speed, water, sediment; };

void SpawnDroplet(Droplet& d)
{
	for (int tries = 0; tries < 50; ++tries) {
		int rx = rand() % GSZ, ry = rand() % GSZ;
		if (ground[ry][rx] > 1.5) { d.x = rx + 0.5; d.y = ry + 0.5; break; }
		if (tries == 49) { d.x = GSZ * 0.5; d.y = GSZ * 0.5; }
	}
	d.vx = d.vy = 0.0; d.speed = 1.0; d.water = 1.0; d.sediment = 0.0;
}

void ErosionStep()
{
	if (!erosionActive || erosionCounter++ > MAX_EROSION_STEPS) return;

	for (int n = 0; n < dropletsPerFrame; ++n) {
		Droplet d; SpawnDroplet(d);

		for (int life = 0; life < DROPLET_LIFE; ++life)
		{
			if (d.x <= 1 || d.x >= GSZ - 2 || d.y <= 1 || d.y >= GSZ - 2) break;

			double h = SampleHeight(d.x, d.y);
			double gx, gy; SampleGradient(d.x, d.y, gx, gy);

			d.vx = d.vx * INERTIA_K - gx * (1.0 - INERTIA_K);
			d.vy = d.vy * INERTIA_K - gy * (1.0 - INERTIA_K);

			double vlen = std::sqrt(d.vx * d.vx + d.vy * d.vy);
			if (vlen < 1e-6) break;
			d.vx /= vlen; d.vy /= vlen;

			d.x += d.vx; d.y += d.vy;
			if (d.x <= 1 || d.x >= GSZ - 2 || d.y <= 1 || d.y >= GSZ - 2) break;

			double h2 = SampleHeight(d.x, d.y);
			double dh = h2 - h;

			d.speed = std::sqrt(std::max(0.0, d.speed * d.speed + (-dh) * GRAVITY));
			d.speed *= (1.0 - FRICTION);

			double slopeMag = std::max(1e-4, std::sqrt(gx * gx + gy * gy));
			double capacity = std::max(MIN_CAP, CAPACITY_K * slopeMag * d.speed * d.water);

			if (dh >= 0.0 && slopeMag < SLOPE_DEPO_LIMIT) {
				double surplus = d.sediment - capacity;
				if (surplus > 0.0) {
					double give = std::min(surplus * DEPOSITION, MAX_DEPOSIT_PER_STEP);
					d.sediment -= give;
					ApplyDepositionBrush((int)d.x, (int)d.y, give);
					ThermalRelax((int)d.x, (int)d.y);
				}
			}
			else {
				double deficit = capacity - d.sediment;
				if (deficit > 0.0) {
					double need = std::min(deficit * EROSION, MAX_ERODE_PER_STEP);
					ApplyErosionBrush((int)d.x, (int)d.y, need);
					d.sediment += need;
				}
			}

			d.water *= (1.0 - EVAPORATION);
			if (d.water < 0.05) break;

			flow[(int)d.y][(int)d.x] += d.water * d.speed;
		}
	}
}


void DrawWall()
{
	glBegin(GL_POLYGON);
	glVertex3d(-4, 0, 0);
	glVertex3d(-4, 3, 0);
	glVertex3d(-3, 3, 0);
	glVertex3d(-3, 0, 0);
	glEnd();

	glBegin(GL_POLYGON);
	glVertex3d(-3, 0, 0);
	glVertex3d(-3, 1, 0);
	glVertex3d(-2, 1, 0);
	glVertex3d(-2, 0, 0);
	glEnd();

	glBegin(GL_POLYGON);
	glVertex3d(-3, 2, 0);
	glVertex3d(-3, 3, 0);
	glVertex3d(-2, 3, 0);
	glVertex3d(-2, 2, 0);
	glEnd();

	glBegin(GL_POLYGON);
	glVertex3d(-2, 0, 0);
	glVertex3d(-2, 3, 0);
	glVertex3d(-1, 3, 0);
	glVertex3d(-1, 0, 0);
	glEnd();

	glBegin(GL_POLYGON);
	glVertex3d(-1, 0, 0);
	glVertex3d(-1, 3, 0);
	glVertex3d(1, 3, 0);
	glVertex3d(1, 0, 0);
	glEnd();

	glBegin(GL_POLYGON);
	glVertex3d(4, 0, 0);
	glVertex3d(4, 3, 0);
	glVertex3d(3, 3, 0);
	glVertex3d(3, 0, 0);
	glEnd();

	glBegin(GL_POLYGON);
	glVertex3d(3, 0, 0);
	glVertex3d(3, 1, 0);
	glVertex3d(2, 1, 0);
	glVertex3d(2, 0, 0);
	glEnd();

	glBegin(GL_POLYGON);
	glVertex3d(3, 2, 0);
	glVertex3d(3, 3, 0);
	glVertex3d(2, 3, 0);
	glVertex3d(2, 2, 0);
	glEnd();

	glBegin(GL_POLYGON);
	glVertex3d(2, 0, 0);
	glVertex3d(2, 3, 0);
	glVertex3d(1, 3, 0);
	glVertex3d(1, 0, 0);
	glEnd();
}

void DrawOneStore()
{
	glColor3d(0.5, 0.3, 0.0);
	glBegin(GL_POLYGON);
	glVertex3d(-4, 0, 0);
	glVertex3d(-4, 0, -8);
	glVertex3d(4, 0, -8);
	glVertex3d(4, 0, 0);
	glEnd();

	glColor3d(0.9, 0.8, 0.5);
	DrawWall();

	glPushMatrix();
	glTranslated(4, 0, -4);
	glRotated(90, 0, 1, 0);
	DrawWall();
	glPopMatrix();

	glPushMatrix();
	glTranslated(-4, 0, -4);
	glRotated(-90, 0, 1, 0);
	DrawWall();
	glPopMatrix();

	glPushMatrix();
	glTranslated(0, 0, -8);
	DrawWall();
	glPopMatrix();
}

void DrawRoof()
{
	glColor3d(0.75, 0.2, 0.2);
	glBegin(GL_POLYGON);
	glVertex3d(-4, 0, 0);
	glVertex3d(0, 1, -4);
	glVertex3d(4, 0, 0);
	glEnd();

	glPushMatrix();
	glTranslated(4, 0, -4);
	glRotated(90, 0, 1, 0);
	glBegin(GL_POLYGON);
	glVertex3d(-4, 0, 0);
	glVertex3d(0, 1, -4);
	glVertex3d(4, 0, 0);
	glEnd();
	glPopMatrix();

	glPushMatrix();
	glTranslated(-4, 0, -4);
	glRotated(-90, 0, 1, 0);
	glBegin(GL_POLYGON);
	glVertex3d(-4, 0, 0);
	glVertex3d(0, 1, -4);
	glVertex3d(4, 0, 0);
	glEnd();
	glPopMatrix();

	glPushMatrix();
	glTranslated(0, 0, -8);
	glRotated(180, 0, 1, 0);
	glBegin(GL_POLYGON);
	glVertex3d(-4, 0, 0);
	glVertex3d(0, 1, -4);
	glVertex3d(4, 0, 0);
	glEnd();
	glPopMatrix();
}


void DrawHouse()
{
	DrawOneStore();
	glPushMatrix();
	glTranslated(0, 3, 0);
	DrawOneStore();
	glPopMatrix();
	glPushMatrix();
	glTranslated(0, 6, 0.4);
	glScaled(1.1, 4, 1.1);
	DrawRoof();
	glPopMatrix();
}

void DrawPlacedHouses()
{
	for (const auto& h : houses) {
		const double wx = h.x - GSZ / 2.0;
		const double wz = h.y - GSZ / 2.0;
		const double wy = SampleHeight(h.x + 0.5, h.y + 0.5) + 0.08;

		glPushMatrix();
		glTranslated(wx, wy, wz);
		glRotated(h.rotDeg, 0, 1, 0);

		const double base = 0.15;
		const double var = 0.90 + (rand() % 21) / 100.0;
		glScaled(base * var, base * h.hscale, base * var);

		DrawHouse();
		glPopMatrix();
	}
}

static inline bool IsFlatPatch(int x, int y, int r, double maxDelta)
{
	double mn = 1e9, mx = -1e9;
	for (int dy = -r; dy <= r; ++dy)
		for (int dx = -r; dx <= r; ++dx) {
			int nx = x + dx, ny = y + dy;
			if (nx < 0 || ny < 0 || nx >= GSZ || ny >= GSZ) continue;
			double h = ground[ny][nx];
			mn = std::min(mn, h); mx = std::max(mx, h);
		}
	return (mx - mn) <= maxDelta;
}

static void BuildWaterMask(std::vector<std::pair<int, int>>& waterCells)
{
	waterCells.clear();
	double maxFlow = 0.0;
	for (int i = 0; i < GSZ; ++i)
		for (int j = 0; j < GSZ; ++j)
			maxFlow = std::max(maxFlow, flow[i][j]);

	const double thr = std::max(0.003, maxFlow * 0.20);

	for (int i = 0; i < GSZ; ++i)
		for (int j = 0; j < GSZ; ++j)
			if (ground[i][j] <= SEA_LEVEL + 0.02 || flow[i][j] >= thr)
				waterCells.emplace_back(j, i);
}

static inline bool IsValidLot(int x, int y,
	const std::vector<std::pair<int, int>>& waterCells,
	double& nearestWaterH)
{
	if (x < 2 || y < 2 || x >= GSZ - 2 || y >= GSZ - 2) return false;

	double h = ground[y][x];
	if (h < SEA_LEVEL + SAFE_MARGIN) return false;
	if (h > MAX_ELEV_FOR_HOUSE)      return false;
	if (!IsFlatPatch(x, y, FLAT_RADIUS, FLAT_MAX_DELTA)) return false;

	bool nearWater = false;
	double bestD2 = 1e9, bestH = h;

	for (const auto& wc : waterCells) {
		int dx = wc.first - x, dy = wc.second - y;
		int d2 = dx * dx + dy * dy;
		if (d2 <= 16) {
			nearWater = true;
			if (d2 < bestD2) { bestD2 = (double)d2; bestH = ground[wc.second][wc.first]; }
		}
	}
	if (!nearWater) return false;
	if (std::fabs(h - bestH) > BANK_MAX_RISE) return false;

	nearestWaterH = bestH;
	return true;
}

void PlaceHouses()
{
	if (housesPlaced) { std::printf("Houses already placed.\n"); return; }
	if (erosionActive) { std::printf("Stop erosion first, then place houses.\n"); return; }

	std::vector<std::pair<int, int>> waterCells;
	BuildWaterMask(waterCells);

	int anchorX = -1, anchorY = -1;
	double dummyH = 0.0;

	for (int tries = 0; tries < 6000; ++tries) {
		int x = 2 + rand() % (GSZ - 4);
		int y = 2 + rand() % (GSZ - 4);
		if (IsValidLot(x, y, waterCells, dummyH)) { anchorX = x; anchorY = y; break; }
	}

	if (anchorX < 0) { std::printf("Could not find a valid city anchor.\n"); housesPlaced = true; return; }

	houses.push_back({ anchorX, anchorY,
					   0.12 + (rand() % 9) / 100.0,
					   (double)(rand() % 360),
					   0.75 + (rand() % 21) / 100.0 });

	int attempts = 0;
	while ((int)houses.size() < MAX_HOUSES && attempts < CITY_CANDIDATE_TRIES)
	{
		attempts++;

		double r = rand() / (double)RAND_MAX; r *= r;
		r *= CITY_RADIUS_CELLS;
		double ang = (rand() / (double)RAND_MAX) * 2.0 * PI;

		int x = anchorX + (int)std::lround(r * std::cos(ang));
		int y = anchorY + (int)std::lround(r * std::sin(ang));

		double nearWaterH = 0.0;
		if (!IsValidLot(x, y, waterCells, nearWaterH)) continue;

		bool tooClose = false;
		for (const auto& hh : houses) {
			int dx = hh.x - x, dy = hh.y - y;
			if (dx * dx + dy * dy < CITY_MIN_SPACING * CITY_MIN_SPACING) { tooClose = true; break; }
		}
		if (tooClose) continue;

		houses.push_back({ x, y,
						   0.12 + (rand() % 9) / 100.0,
						   (double)(rand() % 360),
						   0.75 + (rand() % 21) / 100.0 });
	}

	housesPlaced = true;
	std::printf("City placed: %d houses (anchor %d,%d; attempts=%d)\n",
		(int)houses.size(), anchorX, anchorY, attempts);
}


void DrawGround()
{
	glEnable(GL_POLYGON_OFFSET_FILL);
	glPolygonOffset(1.0f, 1.0f);

	for (int i = 1; i < GSZ; i++)
		for (int j = 1; j < GSZ; j++) {
			glBegin(GL_POLYGON);
			SetColor(ground[i][j - 1]);
			glVertex3d(j - 1 - GSZ / 2, ground[i][j - 1], i - GSZ / 2);
			SetColor(ground[i - 1][j - 1]);
			glVertex3d(j - 1 - GSZ / 2, ground[i - 1][j - 1], i - 1 - GSZ / 2);
			SetColor(ground[i - 1][j]);
			glVertex3d(j - GSZ / 2, ground[i - 1][j], i - 1 - GSZ / 2);
			SetColor(ground[i][j]);
			glVertex3d(j - GSZ / 2, ground[i][j], i - GSZ / 2);
			glEnd();
		}

	glDisable(GL_POLYGON_OFFSET_FILL);

	for (int i = 1; i < GSZ; i++)
		for (int j = 1; j < GSZ; j++) {
			double f = (flow[i][j] + flow[i - 1][j] + flow[i][j - 1] + flow[i - 1][j - 1]) * 0.25;
			if (f > FLOW_THR) {
				double a = std::min(0.6, f * 0.02);
				glEnable(GL_BLEND);
				glBlendFunc(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA);
				glColor4d(0.0, 0.35, 0.9, a);
				const double lift = 0.015;
				glBegin(GL_POLYGON);
				glVertex3d(j - 1 - GSZ / 2, ground[i][j - 1] + lift, i - GSZ / 2);
				glVertex3d(j - 1 - GSZ / 2, ground[i - 1][j - 1] + lift, i - 1 - GSZ / 2);
				glVertex3d(j - GSZ / 2, ground[i - 1][j] + lift, i - 1 - GSZ / 2);
				glVertex3d(j - GSZ / 2, ground[i][j] + lift, i - GSZ / 2);
				glEnd();
				glDisable(GL_BLEND);
			}
		}

	glEnable(GL_BLEND);
	glBlendFunc(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA);
	glColor4d(0, 0.4, 0.8, 0.6);
	glBegin(GL_POLYGON);
	glVertex3d(-GSZ / 2, -0.05, -GSZ / 2);
	glVertex3d(-GSZ / 2, -0.05, GSZ / 2);
	glVertex3d(GSZ / 2, -0.05, GSZ / 2);
	glVertex3d(GSZ / 2, -0.05, -GSZ / 2);
	glEnd();
	glDisable(GL_BLEND);

	DrawPlacedHouses();
}

void display()
{
	glClear(GL_COLOR_BUFFER_BIT | GL_DEPTH_BUFFER_BIT);
	glMatrixMode(GL_PROJECTION);
	glLoadIdentity();
	glFrustum(-1, 1, -1, 1, 0.8, 300);

	gluLookAt(eye[0], eye[1], eye[2],
		eye[0] + dir[0], eye[1] + dir[1], eye[2] + dir[2],
		0, 1, 0);

	glMatrixMode(GL_MODELVIEW);
	glLoadIdentity();
	DrawGround();
	glutSwapBuffers();
}

void displayTop()
{
	glClear(GL_COLOR_BUFFER_BIT | GL_DEPTH_BUFFER_BIT);
	glMatrixMode(GL_PROJECTION);
	glLoadIdentity();
	glFrustum(-1, 1, -1, 1, 0.8, 300);

	gluLookAt(eye[0], 70, eye[2],
		eye[0] + dir[0], 60, eye[2] + dir[2],
		0, 1, 0);

	glMatrixMode(GL_MODELVIEW);
	glLoadIdentity();
	DrawGround();
	glutSwapBuffers();
}

void init()
{
	glClearColor(0.7, 0.8, 1, 0);
	glEnable(GL_DEPTH_TEST);

	lastErosionTime = steady_clock::now();
	srand((unsigned int)time(0));

	SetupTerrain(800);
	Smooth();
	SetupTerrain(30);

	for (int i = 0; i < GSZ; i++)
		for (int j = 0; j < GSZ; j++)
			ground[i][j] += 1.0;
}

void idle()
{
	for (int i = 0; i < GSZ; i++)
		for (int j = 0; j < GSZ; j++)
			flow[i][j] *= 0.995;

	if (erosionActive) {
		auto now = steady_clock::now();
		if (duration_cast<milliseconds>(now - lastErosionTime).count() > erosionDelayMs) {
			ErosionStep();
			lastErosionTime = now;
		}
	}

	sight_angle += angular_speed;
	dir[0] = std::sin(sight_angle);
	dir[1] = -0.3;
	dir[2] = std::cos(sight_angle);
	eye[0] += speed * dir[0];
	eye[2] += speed * dir[2];

	glutPostRedisplay();
}

void SpecialKeys(int key, int, int)
{
	switch (key) {
	case GLUT_KEY_DOWN:
		speed -= 0.01; break;
	case GLUT_KEY_UP:
		speed += 0.01; break;
	case GLUT_KEY_LEFT:
		angular_speed += 0.001; break;
	case GLUT_KEY_RIGHT:
		angular_speed -= 0.001; break;
	case GLUT_KEY_PAGE_UP:
		eye[1] += 0.1; break;
	case GLUT_KEY_PAGE_DOWN:
		eye[1] -= 0.1; break;
	}
}

void menu(int choice)
{
	switch (choice) {
	case 1: glutDisplayFunc(display);    break;
	case 2: glutDisplayFunc(displayTop); break;
	case 3: PlaceHouses();               break;
	case 4:
		erosionActive = true;
		if (!erosionStarted) {
			erosionStarted = true;
			erosionCounter = 0;
			lastErosionTime = steady_clock::now();
			std::printf("Erosion started.\n");
		}
		break;
	case 5:
		erosionActive = false;
		std::printf("Erosion paused.\n");
		break;
	case 6:
		Smooth();
		std::printf("Smoothed.\n");
		break;
	}
}

void Mouse(int button, int state, int, int)
{
	if (button == GLUT_LEFT_BUTTON && state == GLUT_DOWN) {
		erosionActive = false;
		Smooth();
	}
}

int main(int argc, char* argv[])
{
	glutInit(&argc, argv);
	glutInitDisplayMode(GLUT_RGB | GLUT_DOUBLE | GLUT_DEPTH);
	glutInitWindowSize(800, 800);
	glutInitWindowPosition(200, 50);
	glutCreateWindow("Terrain + Hydraulic Erosion + Houses");

	glutDisplayFunc(display);
	glutIdleFunc(idle);
	glutSpecialFunc(SpecialKeys);

	glutCreateMenu(menu);
	glutAddMenuEntry("Regular View", 1);
	glutAddMenuEntry("Top View", 2);
	glutAddMenuEntry("Place Houses", 3);
	glutAddMenuEntry("Start Erosion", 4);
	glutAddMenuEntry("Stop Erosion", 5);
	glutAddMenuEntry("Smooth Once", 6);
	glutAttachMenu(GLUT_RIGHT_BUTTON);

	glutMouseFunc(Mouse);

	init();
	glutMainLoop();
	return 0;
}
