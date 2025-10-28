/*
 * Copyright (C) 2019-2025 SkyLabs AI.
 *
 * SPDX-License-Identifier:MIT-0
 */

class Point {
private:
    int x, y;

public:
    Point(int _x, int _y):x(_x),y(_y) {}

    ~Point() {}

    int getX() const { return (*this).x; }
    int getY() const { return this->y; }

    int mdist(const Point &other) const {
        return (other.getX() - (*this).getX()) + (other.getY() - this->getY());
    }
};
